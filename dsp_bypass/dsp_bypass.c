/*
 * dsp_bypass — APatch / KernelPatch KPM that masks root-framework
 * sepolicy rules from userspace SELinux probes (e.g. DirtySepolicy).
 *
 * It wraps security_compute_av_user, the kernel path behind
 * SELinux.checkSELinuxAccess() / writes to /sys/fs/selinux/access, and
 * zeroes avd->allowed for queries that target a "dirty" SID or match a
 * known dirty (scon, tcon) pair. In-kernel AVC checks via
 * security_compute_av are untouched, so the root framework itself keeps
 * working.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include <compiler.h>
#include <kpmodule.h>
#include <kputils.h>
#include <kallsyms.h>
#include <hook.h>
#include <log.h>
#include <linux/security.h>
#include <linux/sched.h>
#include <linux/string.h>
#include <linux/gfp.h>
#include <asm/current.h>
#include <uapi/asm-generic/errno.h>

KPM_NAME("dsp_bypass");
KPM_VERSION("1.0.5");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("oMasko");
KPM_DESCRIPTION("Dirty SELinux Bypass");

/* KP's gfp.h leaves these undefined (value varies by kernel). 0xcc0
 * matches modern AOSP GKI: __GFP_RECLAIM | __GFP_IO | __GFP_FS. */
#ifndef GFP_KERNEL
#define GFP_KERNEL ((gfp_t)0xcc0u)
#endif

/* ---- editable tables --------------------------------------------------- */

/* Targets whose mere appearance in a query is suspicious.
 * These are only masked for a targeted caller selected by module args. */
static const char *const dirty_targets[] = {
    /* Magisk */
    "u:r:magisk:s0", "u:r:magisk_client:s0", "u:object_r:magisk_file:s0", "u:object_r:magisk_exec:s0",
    /* KernelSU */
    "u:r:ksu:s0", "u:r:su:s0", "u:object_r:ksu_exec:s0", "u:object_r:ksu_file:s0",
    /* APatch */
    "u:r:apatch:s0", "u:r:apatch_lite:s0", "u:object_r:apatch_exec:s0", "u:object_r:apatch_file:s0",
    /* LSPosed / Xposed */
    "u:object_r:lsposed_file:s0", "u:object_r:xposed_data:s0",
    /* adb_root */
    "u:r:adbroot:s0", 0
};

/* Contexts to hide from raw /sys/fs/selinux/context probes. */
static const char *const blocked_ctx_cfg[] = { "u:r:magisk:s0",
                                               "u:r:ksu:s0",
                                               "u:r:apatch:s0",
                                               "u:object_r:magisk_file:s0",
                                               "u:object_r:ksu_file:s0",
                                               "u:object_r:apatch_file:s0",
                                               "u:object_r:lsposed_file:s0",
                                               0 };

/* (scon, tcon) pairs that are dirty only as a combination — both endpoints
 * are legitimate AOSP types, but the allow rule itself shouldn't exist. */
static const struct
{
    const char *s, *t;
} dirty_pairs_cfg[] = { { "u:r:zygote:s0", "u:object_r:adb_data_file:s0" }, /* ZygiskNext */
                        { "u:r:system_server:s0", "u:r:system_server:s0" }, /* execmem neverallow */
                        { "u:r:fsck_untrusted:s0", "u:r:fsck_untrusted:s0" }, /* sys_admin neverallow */
                        { "u:r:untrusted_app:s0", "u:object_r:lsposed_file:s0" }, /* LSPosed dirty policy */
                        { "u:r:adbd:s0", "u:r:adbroot:s0" }, /* adb root binder probe */
                        { "u:r:app_zygote:s0", "u:object_r:ksu_file:s0" }, /* Oracle carrier -> root obj */
                        { "u:r:app_zygote:s0", "u:object_r:magisk_file:s0" }, /* Oracle carrier -> root obj */
                        { "u:r:app_zygote:s0:c512,c768", "u:object_r:ksu_file:s0" },
                        { "u:r:app_zygote:s0:c512,c768", "u:object_r:magisk_file:s0" },
                        { 0, 0 } };

/* ---- kernel ABI we touch ----------------------------------------------- */

/*
 * security_compute_av_user, security_context_to_sid and avc_ss_reset all
 * gained a `struct selinux_state *` first argument in 5.0 and lost it
 * again in 6.6. We detect that ABI by probing for the `selinux_state`
 * global symbol — it only exists when the parameter does.
 */
struct av_decision_compat
{
    uint32_t allowed, auditallow, auditdeny, seqno, flags;
};

typedef int (*ctx_to_sid_4_t)(const char *, uint32_t, uint32_t *, gfp_t);
typedef int (*ctx_to_sid_5_t)(void *, const char *, uint32_t, uint32_t *, gfp_t);
typedef int (*avc_reset_1_t)(uint32_t);
typedef int (*get_cmdline_t)(struct task_struct *, char *, int);

/* reverse direction: SID -> context string, used to read the CURRENT
 * task's actual SELinux domain rather than trust its process name. */
typedef int (*sid_to_ctx_4_t)(uint32_t, char **, uint32_t *);
typedef int (*sid_to_ctx_5_t)(void *, uint32_t, char **, uint32_t *);
typedef void (*getsecid_t)(struct task_struct *, uint32_t *);
typedef void (*kfree_t)(const void *);

/* ---- module state ------------------------------------------------------ */

#define MAX_TARGETS 64
#define MAX_PAIRS 16

static void *fn_ctx_to_sid, *fn_avc_reset, *selinux_state_p;
static void *fn_compute_av_user, *fn_load_policy;
static void *fn_avc_denied;
static void *fn_slow_avc_audit;
static get_cmdline_t fn_get_cmdline;
static void *fn_sid_to_ctx;
static getsecid_t fn_getsecid;
static kfree_t fn_kfree;
static int has_state;
static int (*avc_denied_backup)(void *, void *, void *, void *, void *, void *, void *, void *) = 0;
static int (*slow_avc_audit_backup)(void *, void *, void *, void *, void *, void *, void *, void *, void *) = 0;

static uint32_t dirty_target_sids[MAX_TARGETS];
static int dirty_target_count;

static struct
{
    uint32_t s, t;
} dirty_pair_sids[MAX_PAIRS];
static int dirty_pair_count;

static int cache_ready;

static const char *blocked_ctx_strings[MAX_TARGETS];
static int blocked_ctx_count;

#define TARGET_NAME_MAX 96
static int uid_filter_enabled;
static uid_t target_uid = (uid_t)-1;
static int package_filter_enabled;
static char target_package[TARGET_NAME_MAX];

/* ---- SID resolution ---------------------------------------------------- */

static int parse_uid_arg(const char *args, uid_t *out)
{
    const char *p;
    char buf[16];
    int i = 0;
    long long value = 0;

    if (!args || !out) return 0;
    p = strstr(args, "uid=");
    if (!p) return 0;
    p += 4;

    while (p[i] && p[i] != ',' && p[i] != ' ' && p[i] != '\n' && i < (int)sizeof(buf) - 1) {
        buf[i] = p[i];
        i++;
    }
    if (i == 0) return -1;
    buf[i] = '\0';

    if (kstrtoll(buf, 10, &value) || value < 0) return -1;
    *out = (uid_t)value;
    return 1;
}

static int parse_package_arg(const char *args, char *out, int out_size)
{
    const char *p;
    int i = 0;

    if (!args || !out || out_size <= 1) return 0;
    p = strstr(args, "package=");
    if (!p) return 0;
    p += 8;

    while (p[i] && p[i] != ',' && p[i] != ' ' && p[i] != '\n' && i < out_size - 1) {
        out[i] = p[i];
        i++;
    }
    if (i == 0) return -1;
    out[i] = '\0';
    return 1;
}

static int targeting_enabled(void)
{
    return uid_filter_enabled || package_filter_enabled;
}

static void log_filters(void)
{
    if (uid_filter_enabled) logkd("dsp_bypass: uid filter=%u\n", target_uid);
    if (package_filter_enabled) logkd("dsp_bypass: package filter=%s\n", target_package);
    if (!targeting_enabled()) logkd("dsp_bypass: no target filter configured; bypass stays inactive\n");
    logkd("dsp_bypass: domain-match ready=%s\n", (fn_getsecid && fn_sid_to_ctx) ? "yes" : "no (comm/cmdline only)");
}

static void apply_filters_from_args(const char *args)
{
    uid_t parsed_uid;
    char parsed_package[TARGET_NAME_MAX];
    int ret;

    uid_filter_enabled = 0;
    package_filter_enabled = 0;
    target_uid = (uid_t)-1;
    target_package[0] = '\0';

    ret = parse_uid_arg(args, &parsed_uid);
    if (ret == 1) {
        uid_filter_enabled = 1;
        target_uid = parsed_uid;
    }

    ret = parse_package_arg(args, parsed_package, sizeof(parsed_package));
    if (ret == 1) {
        package_filter_enabled = 1;
        strcpy(target_package, parsed_package);
    }
}

static void log_target_hit(const char *reason, const char *detail)
{
    char cmdline[128];
    const char *comm;
    int len = 0;

    cmdline[0] = '\0';
    if (fn_get_cmdline) {
        len = fn_get_cmdline(current, cmdline, sizeof(cmdline) - 1);
        if (len > 0) cmdline[len] = '\0';
    }

    comm = get_task_comm(current);
    logkd("dsp_bypass: %s uid=%u comm=%s cmdline=%s detail=%s\n", reason, current_uid(), comm ? comm : "<null>",
          cmdline[0] ? cmdline : "<none>", detail ? detail : "<none>");
}

/*
 * Resolve the CURRENT task's actual SELinux domain (via its SID) and
 * check whether its TYPE component is "app_zygote". This is the signal
 * Duck Detector itself relies on ("dedicated app_zygote carrier") and is
 * far more reliable than comm/cmdline: a probe process can rename itself
 * (Process.setArgV0) before running the probe, but it cannot change the
 * SELinux domain it was forked into without an actual domain transition.
 * We only compare the type prefix "u:r:app_zygote:s0" and ignore the MLS
 * category suffix (:c512,c768, ...), since that varies per instance.
 */
/* Resolve the CURRENT task's SID to its context string, copied into
 * out (caller-owned, up to out_size-1 bytes). Returns 1 on success, 0
 * if the symbols are missing or resolution failed for any reason. */
static int resolve_current_domain_ctx(char *out, int out_size)
{
    uint32_t secid = 0;
    char *ctx = 0;
    uint32_t ctx_len = 0;
    int ret;
    int ok = 0;

    if (!out || out_size <= 1) return 0;
    out[0] = '\0';

    if (!fn_getsecid || !fn_sid_to_ctx) return 0;

    fn_getsecid(current, &secid);
    if (!secid) return 0;

    ret = has_state ? ((sid_to_ctx_5_t)fn_sid_to_ctx)(selinux_state_p, secid, &ctx, &ctx_len) :
                      ((sid_to_ctx_4_t)fn_sid_to_ctx)(secid, &ctx, &ctx_len);

    if (ret == 0 && ctx) {
        int n = (int)strlen(ctx);
        if (n >= out_size) n = out_size - 1;
        memcpy(out, ctx, n);
        out[n] = '\0';
        ok = 1;
        if (fn_kfree) fn_kfree(ctx);
    }

    return ok;
}

static int current_task_is_app_zygote_domain(void)
{
    char ctx[160];

    if (!resolve_current_domain_ctx(ctx, sizeof(ctx))) return 0;
    if (strncmp(ctx, "u:r:app_zygote:s0", 17) == 0) {
        logkd("dsp_bypass: domain-match hit ctx=%s\n", ctx);
        return 1;
    }
    return 0;
}

static int current_matches_target(void)
{
    char cmdline[128];
    int len;
    const char *comm;

    if (!targeting_enabled()) return 0;

    if (uid_filter_enabled && current_uid() != target_uid) return 0;
    if (!package_filter_enabled) return 1;

    /* Strongest signal first: the task's actual SELinux domain, not its
     * (possibly renamed) process name. */
    if (current_task_is_app_zygote_domain()) return 1;

    comm = get_task_comm(current);

    /* Fallback for probes that don't rename themselves at all. */
    if (comm && strcmp(comm, "app_zygote") == 0) return 1;

    if (fn_get_cmdline) {
        len = fn_get_cmdline(current, cmdline, sizeof(cmdline) - 1);
        if (len > 0) {
            cmdline[len] = '\0';
            if (strstr(cmdline, target_package)) return 1;
        }
    }

    if (comm && strstr(comm, target_package)) return 1;
    return 0;
}

static int is_blocked_ctx(const char *ctx)
{
    int i;

    if (!ctx || !current_matches_target()) return 0;
    for (i = 0; i < blocked_ctx_count; i++)
        if (blocked_ctx_strings[i] && strcmp(ctx, blocked_ctx_strings[i]) == 0) return 1;
    return 0;
}

static int is_dirty_query(uint32_t ssid, uint32_t tsid)
{
    int i;

    if (!cache_ready) return 0;
    for (i = 0; i < dirty_target_count; i++)
        if (tsid == dirty_target_sids[i]) return 1;
    for (i = 0; i < dirty_pair_count; i++)
        if (ssid == dirty_pair_sids[i].s && tsid == dirty_pair_sids[i].t) return 1;
    return 0;
}

static void decode_query_pair(void *_state, void *_ssid, void *_tsid, uint32_t *ssid, uint32_t *tsid)
{
    if (has_state) {
        *ssid = (uint32_t)(uintptr_t)_ssid;
        *tsid = (uint32_t)(uintptr_t)_tsid;
    } else {
        *ssid = (uint32_t)(uintptr_t)_state;
        *tsid = (uint32_t)(uintptr_t)_ssid;
    }
}

/* 4-arg: (ctx, len, sid_out, gfp) */
static void pre_ctx_to_sid_4(hook_fargs4_t *f, void *ud)
{
    const char *ctx = (const char *)(uintptr_t)f->arg0;
    if (!is_blocked_ctx(ctx)) return;
    log_target_hit("blocked ctx_to_sid", ctx);
    f->skip_origin = 1;
    f->ret = (uint64_t)(int64_t)-EINVAL;
}

/* 5-arg: (state, ctx, len, sid_out, gfp) */
static void pre_ctx_to_sid_5(hook_fargs8_t *f, void *ud)
{
    const char *ctx = (const char *)(uintptr_t)f->arg1;
    if (!is_blocked_ctx(ctx)) return;
    log_target_hit("blocked ctx_to_sid", ctx);
    f->skip_origin = 1;
    f->ret = (uint64_t)(int64_t)-EINVAL;
}

static int lookup_sid(const char *ctx, uint32_t *out)
{
    if (!fn_ctx_to_sid) return -1;
    if (has_state) return ((ctx_to_sid_5_t)fn_ctx_to_sid)(selinux_state_p, ctx, strlen(ctx), out, GFP_KERNEL);
    return ((ctx_to_sid_4_t)fn_ctx_to_sid)(ctx, strlen(ctx), out, GFP_KERNEL);
}

static void resolve_sids(void)
{
    uint32_t s, t;
    int i, n = 0, p = 0, bc = 0;

    for (i = 0; dirty_targets[i] && n < MAX_TARGETS; i++) {
        if (lookup_sid(dirty_targets[i], &t) == 0 && t) {
            dirty_target_sids[n++] = t;
        }
    }
    dirty_target_count = n;

    for (i = 0; blocked_ctx_cfg[i] && bc < MAX_TARGETS; i++)
        if (lookup_sid(blocked_ctx_cfg[i], &t) == 0 && t) blocked_ctx_strings[bc++] = blocked_ctx_cfg[i];
    blocked_ctx_count = bc;

    for (i = 0; dirty_pairs_cfg[i].s && p < MAX_PAIRS; i++)
        if (lookup_sid(dirty_pairs_cfg[i].s, &s) == 0 && s && lookup_sid(dirty_pairs_cfg[i].t, &t) == 0 && t) {
            dirty_pair_sids[p].s = s;
            dirty_pair_sids[p].t = t;
            p++;
        }
    dirty_pair_count = p;
    cache_ready = (n || p);

    logkd("dsp_bypass: cached %d targets, %d blocked ctx, %d pairs\n", n, bc, p);

    /* In the state-passing era avc_ss_reset takes (avc, seqno); we'd
     * have to guess the field offset, so skip it there. Stale 'allow'
     * decisions age out of the AVC within seconds anyway. */
    if (!has_state && fn_avc_reset) ((avc_reset_1_t)fn_avc_reset)(0);
}

/* ---- hot path ---------------------------------------------------------- */

static void diag_log_call(const char *where, uint32_t ssid, uint32_t tsid, int match, int dirty)
{
    char domain[160];
    const char *comm;
    int got_domain;

    /* Log only calls that are actually relevant: either our own
     * matching logic already says yes, OR the query itself touches a
     * dirty target SID (adbroot/ksu/magisk/...) regardless of who is
     * asking. This is what lets us catch the real probe even when
     * current_matches_target() is wrong about the caller, while cutting
     * out the heavy background noise from servicemanager,
     * hwservicemanager, keystore, etc., which never touch these SIDs at
     * all and would otherwise bury the one line that matters. */
    if (!match && !dirty) return;

    got_domain = resolve_current_domain_ctx(domain, sizeof(domain));
    comm = get_task_comm(current);
    logkd("dsp_bypass: DIAG %s uid=%u comm=%s domain=%s ssid=%u tsid=%u match=%d dirty=%d\n", where,
          current_uid(), comm ? comm : "<null>", got_domain ? domain : "<unresolved>", ssid, tsid, match, dirty);
}

static int scrub(uint32_t ssid, uint32_t tsid, struct av_decision_compat *avd)
{
    int match = current_matches_target();
    int dirty = cache_ready ? is_dirty_query(ssid, tsid) : 0;

    diag_log_call("compute_av_user", ssid, tsid, match, dirty);

    if (!match) return 0;
    if (!cache_ready || !avd) return 0;
    if (!dirty) return 0;

    avd->allowed = avd->auditallow = 0;
    avd->auditdeny = ~0u;
    log_target_hit("scrubbed compute_av_user", "matched dirty policy target");
    return 1;
}

static int slow_avc_audit_replace(void *_state, void *_ssid, void *_tsid, void *_tclass, void *_requested,
                                  void *_audited, void *_denied, void *_result, void *_a)
{
    uint32_t ssid;
    uint32_t tsid;

    if (!slow_avc_audit_backup) return 0;

    decode_query_pair(_state, _ssid, _tsid, &ssid, &tsid);
    diag_log_call("slow_avc_audit", ssid, tsid, current_matches_target(), cache_ready ? is_dirty_query(ssid, tsid) : 0);

    if (!current_matches_target())
        return slow_avc_audit_backup(_state, _ssid, _tsid, _tclass, _requested, _audited, _denied, _result, _a);

    if (is_dirty_query(ssid, tsid)) {
        log_target_hit("suppressed slow_avc_audit", "matched dirty policy target");
        return 0;
    }

    return slow_avc_audit_backup(_state, _ssid, _tsid, _tclass, _requested, _audited, _denied, _result, _a);
}

static int avc_denied_replace(void *_state, void *_ssid, void *_tsid, void *_tclass, void *_requested, void *_driver,
                              void *_xperm, void *_flags)
{
    uint32_t ssid;
    uint32_t tsid;
    struct av_decision_compat *avd;

    if (!avc_denied_backup) return 0;

    decode_query_pair(_state, _ssid, _tsid, &ssid, &tsid);
    diag_log_call("avc_denied", ssid, tsid, current_matches_target(), cache_ready ? is_dirty_query(ssid, tsid) : 0);

    if (!current_matches_target())
        return avc_denied_backup(_state, _ssid, _tsid, _tclass, _requested, _driver, _xperm, _flags);

    if (!is_dirty_query(ssid, tsid))
        return avc_denied_backup(_state, _ssid, _tsid, _tclass, _requested, _driver, _xperm, _flags);

    avd = (struct av_decision_compat *)_flags;
    if (!has_state) avd = (struct av_decision_compat *)_xperm;
    if (avd) {
        avd->allowed = ~0u;
        avd->auditallow = 0;
        avd->auditdeny = 0;
    }

    log_target_hit("suppressed avc_denied", "matched dirty policy target");
    return 0;
}

/* 4-arg: (ssid, tsid, tclass, avd) */
static void post_compute_av_4(hook_fargs4_t *f, void *ud)
{
    scrub((uint32_t)f->arg0, (uint32_t)f->arg1, (struct av_decision_compat *)(uintptr_t)f->arg3);
}

/* 5-arg: (state, ssid, tsid, tclass, avd) — fargs5_t aliases fargs8_t */
static void post_compute_av_5(hook_fargs8_t *f, void *ud)
{
    scrub((uint32_t)f->arg1, (uint32_t)f->arg2, (struct av_decision_compat *)(uintptr_t)f->arg4);
}

static void post_load_policy(hook_fargs2_t *f, void *ud)
{
    if ((long)f->ret == 0) resolve_sids();
}

/* ---- entry points ------------------------------------------------------ */

static long dsp_init(const char *args, const char *event, void *__user reserved)
{
    hook_err_t err;
    hook_err_t err_ctx;

    selinux_state_p = (void *)kallsyms_lookup_name("selinux_state");
    has_state = selinux_state_p != 0;

    fn_ctx_to_sid = (void *)kallsyms_lookup_name("security_context_to_sid");
    fn_compute_av_user = (void *)kallsyms_lookup_name("security_compute_av_user");
    fn_avc_reset = (void *)kallsyms_lookup_name("avc_ss_reset");
    fn_load_policy = (void *)kallsyms_lookup_name("security_load_policy");
    fn_avc_denied = (void *)kallsyms_lookup_name("avc_denied");
    fn_slow_avc_audit = (void *)kallsyms_lookup_name("slow_avc_audit");
    fn_get_cmdline = (get_cmdline_t)kallsyms_lookup_name("get_cmdline");
    if (!fn_load_policy) fn_load_policy = (void *)kallsyms_lookup_name("selinux_policy_load");

    /* Domain-based matching: best-effort, several possible symbol names
     * depending on kernel version. Missing any of these just falls back
     * to comm/cmdline matching, it isn't fatal. */
    fn_getsecid = (getsecid_t)kallsyms_lookup_name("security_task_getsecid_subj");
    if (!fn_getsecid) fn_getsecid = (getsecid_t)kallsyms_lookup_name("security_task_getsecid_obj");
    if (!fn_getsecid) fn_getsecid = (getsecid_t)kallsyms_lookup_name("security_task_getsecid");
    fn_sid_to_ctx = (void *)kallsyms_lookup_name("security_sid_to_context");
    if (!fn_sid_to_ctx) fn_sid_to_ctx = (void *)kallsyms_lookup_name("security_sid_to_context_force");
    fn_kfree = (kfree_t)kallsyms_lookup_name("kfree");

    apply_filters_from_args(args);

    if (!fn_ctx_to_sid || !fn_compute_av_user) {
        logkd("dsp_bypass: missing kernel symbols\n");
        return -ENOENT;
    }

    logkd("dsp_bypass: ABI=%s\n", has_state ? "5.0-6.5" : "<5.0 || >=6.6");
    log_filters();
    resolve_sids();

    err = has_state ? hook_wrap5(fn_compute_av_user, 0, post_compute_av_5, 0) :
                      hook_wrap4(fn_compute_av_user, 0, post_compute_av_4, 0);
    if (err) {
        logkd("dsp_bypass: hook(compute_av_user) failed: %d\n", err);
        return -EFAULT;
    }

    err_ctx = has_state ? hook_wrap5(fn_ctx_to_sid, pre_ctx_to_sid_5, 0, 0) :
                          hook_wrap4(fn_ctx_to_sid, pre_ctx_to_sid_4, 0, 0);
    if (err_ctx) {
        logkd("dsp_bypass: hook(ctx_to_sid) failed: %d\n", err_ctx);
    }

    if (fn_avc_denied) {
        err_ctx = hook(fn_avc_denied, (void *)avc_denied_replace, (void **)&avc_denied_backup);
        if (err_ctx) logkd("dsp_bypass: hook(avc_denied) failed: %d\n", err_ctx);
    }

    if (fn_slow_avc_audit) {
        err_ctx = hook(fn_slow_avc_audit, (void *)slow_avc_audit_replace, (void **)&slow_avc_audit_backup);
        if (err_ctx) logkd("dsp_bypass: hook(slow_avc_audit) failed: %d\n", err_ctx);
    }

    if (fn_load_policy) hook_wrap2(fn_load_policy, 0, post_load_policy, 0);

    return 0;
}

/* `apd module control dsp_bypass <anything>` re-resolves SIDs — handy
 * after pushing extra rules at runtime. */
static long dsp_ctl0(const char *args, char *__user out, int outlen)
{
    apply_filters_from_args(args);
    log_filters();
    resolve_sids();
    return 0;
}

static long dsp_exit(void *__user reserved)
{
    if (fn_compute_av_user) unhook(fn_compute_av_user);
    if (fn_ctx_to_sid) unhook(fn_ctx_to_sid);
    if (fn_avc_denied) unhook(fn_avc_denied);
    if (fn_slow_avc_audit) unhook(fn_slow_avc_audit);
    if (fn_load_policy) unhook(fn_load_policy);
    return 0;
}

KPM_INIT(dsp_init);
KPM_CTL0(dsp_ctl0);
KPM_EXIT(dsp_exit);
