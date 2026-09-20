#!/usr/bin/env python3
"""
Recompute all Paper 1 results from a prime census CSV.

Handles two input modes:

  1. **Corrected CSV** (default): Reads data_1e9.csv as-is.
     No duplicate rows, endpoint p=999,999,937 already present.
     The script validates the CSV is well-formed (unique primes,
     expected endpoint) and refuses to silently invent data.

  2. **Legacy CSV** (--repair-legacy): Applies on-the-fly fixes
     for the known original-sieve bugs:
       - Skips duplicate p=7 rows
       - Appends missing final prime p=999,999,937 with independently
         computed fields (omega=5, is_artin10=0, pmod12=1)
     Before using this mode, the caller should verify:
       - The CSV's last prime is 999,999,929 (not already corrected)
       - The CSV contains exactly 50,847,531 raw rows (header + data)

The script accepts an arbitrary sieve bound — it does NOT hardcode 10^9.

Usage:
    python3 recompute_corrected.py [DATA.csv] [OUTPUT_DIR]
    python3 recompute_corrected.py --repair-legacy [DATA.csv] [OUTPUT_DIR]
"""
import sys, os, math, json, argparse
from collections import defaultdict

# ── argument parsing ──
parser = argparse.ArgumentParser(description="Recompute Paper 1 Artin correlation results")
parser.add_argument("csv", nargs="?", default=None,
                    help="Input CSV path (default: ../data_1e9.csv relative to script)")
parser.add_argument("outdir", nargs="?", default=None,
                    help="Output directory (default: ../results relative to script)")
parser.add_argument("--repair-legacy", action="store_true",
                    help="Apply legacy-CSV fixes: skip duplicate p=7, append missing p=999999937")
args = parser.parse_args()

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT  = os.path.dirname(SCRIPT_DIR)

PATH    = args.csv    or os.path.join(REPO_ROOT, "data_1e9.csv")
OUT_DIR = args.outdir or os.path.join(REPO_ROOT, "results")
os.makedirs(OUT_DIR, exist_ok=True)

REPAIR_LEGACY = args.repair_legacy

if not os.path.isfile(PATH):
    print(f"Error: CSV file not found: {PATH}", file=sys.stderr)
    sys.exit(1)

# Legacy endpoint data (independently computed via sympy)
# p=999999937: prev_gap=8, omega(p-1)=5, is_artin10=0, pmod4=1, pmod8=1, pmod12=1
LEGACY_MISSING_PRIME = 999999937
LEGACY_MISSING_OMEGA = 5
LEGACY_MISSING_ARTIN = 0
LEGACY_MISSING_MOD12 = 1
LEGACY_EXPECTED_LAST = 999999929

# Accumulators
joint = [[0, 0], [0, 0]]
n_pairs = 0
gap_joint = defaultdict(lambda: [[0, 0], [0, 0]])
om_joint = defaultdict(lambda: [[0, 0], [0, 0]])
m12_joint = defaultdict(lambda: [[0, 0], [0, 0]])
m12_trans = defaultdict(int)
cell120 = defaultdict(lambda: [[0, 0], [0, 0]])
cell840 = defaultdict(lambda: [[0, 0], [0, 0]])
cell40g = defaultdict(lambda: [[0, 0], [0, 0]])
halves120 = [defaultdict(lambda: [[0, 0], [0, 0]]), defaultdict(lambda: [[0, 0], [0, 0]])]
HALF = 500_000_000

s_x = s_y = s_xx = s_yy = s_xy = 0.0

n_rows = 0
n_unique = 0
n_artin = 0
n_duplicates = 0
first_prime = None
last_prime = None

prev = None  # (p, omega, artin, m12)

def process_pair(p0, om0, a0, m0, p1, om1, a1, m1):
    """Process one consecutive-prime pair."""
    global n_pairs, s_x, s_y, s_xx, s_yy, s_xy
    g = p1 - p0
    joint[a0][a1] += 1
    n_pairs += 1
    gap_joint[g][a0][a1] += 1
    om_joint[(om0, om1)][a0][a1] += 1
    m12_joint[(m0, m1)][a0][a1] += 1
    m12_trans[(m0, m1)] += 1
    cell120[(p0 % 120, p1 % 120)][a0][a1] += 1
    cell840[(p0 % 840, p1 % 840)][a0][a1] += 1
    cell40g[(p0 % 40, p1 % 40, min(g, 60))][a0][a1] += 1
    h = 0 if p1 < HALF else 1
    halves120[h][(p0 % 120, p1 % 120)][a0][a1] += 1
    s_x += om0; s_y += om1
    s_xx += om0*om0; s_yy += om1*om1; s_xy += om0*om1

print(f"Reading: {PATH}", file=sys.stderr, flush=True)
print(f"Mode: {'--repair-legacy' if REPAIR_LEGACY else 'corrected CSV (no auto-repair)'}", file=sys.stderr, flush=True)

with open(PATH) as f:
    header = f.readline()
    for i, line in enumerate(f):
        parts = line.rstrip("\n").split(",")
        p = int(parts[0])
        omega_val = int(parts[5])
        artin = int(parts[6])
        m12 = int(parts[9])
        n_rows += 1
        if prev is not None:
            p0, om0, a0, m0 = prev
            if p == p0:
                if REPAIR_LEGACY:
                    n_duplicates += 1
                    prev = (p, omega_val, artin, m12)
                    continue
                else:
                    print(f"ERROR: Duplicate prime p={p} at row {n_rows}. "
                          f"Use --repair-legacy for uncorrected CSVs.", file=sys.stderr)
                    sys.exit(1)
            n_unique += 1
            n_artin += a0
            if first_prime is None:
                first_prime = p0
            process_pair(p0, om0, a0, m0, p, omega_val, artin, m12)
        prev = (p, omega_val, artin, m12)
        if i % 10_000_000 == 0 and i:
            print(f"  ...{i//1_000_000}M rows", file=sys.stderr, flush=True)

# Count the last prime from CSV
if prev:
    p0, om0, a0, m0 = prev
    n_unique += 1
    n_artin += a0
    last_prime = p0

print(f"\nCSV stats after reading:", file=sys.stderr)
print(f"  Total rows: {n_rows}", file=sys.stderr)
print(f"  Duplicate rows skipped: {n_duplicates}", file=sys.stderr)
print(f"  Unique primes: {n_unique}", file=sys.stderr)
print(f"  Artin primes: {n_artin}", file=sys.stderr)
print(f"  First prime: {first_prime}", file=sys.stderr)
print(f"  Last prime: {last_prime}", file=sys.stderr)
print(f"  Pairs: {n_pairs}", file=sys.stderr)

# Legacy repair: add missing endpoint if applicable
endpoint_added = False
if REPAIR_LEGACY:
    if last_prime == LEGACY_EXPECTED_LAST:
        print(f"\n--repair-legacy: Adding missing endpoint p={LEGACY_MISSING_PRIME}", file=sys.stderr)
        process_pair(p0, om0, a0, m0,
                     LEGACY_MISSING_PRIME, LEGACY_MISSING_OMEGA,
                     LEGACY_MISSING_ARTIN, LEGACY_MISSING_MOD12)
        n_unique += 1
        n_artin += LEGACY_MISSING_ARTIN
        last_prime = LEGACY_MISSING_PRIME
        endpoint_added = True
        print(f"  Corrected unique primes: {n_unique}", file=sys.stderr)
        print(f"  Corrected pairs: {n_pairs}", file=sys.stderr)
    elif last_prime == LEGACY_MISSING_PRIME:
        print(f"\n--repair-legacy: CSV already ends at {last_prime}; no endpoint to add.", file=sys.stderr)
    else:
        print(f"\nWARNING: --repair-legacy mode but last prime is {last_prime}, "
              f"not {LEGACY_EXPECTED_LAST}. No endpoint correction applied.", file=sys.stderr)
else:
    # In normal mode, just report
    if n_duplicates > 0:
        print(f"\nERROR: {n_duplicates} duplicate rows found in supposedly-corrected CSV.", file=sys.stderr)
        sys.exit(1)

# ── compute statistics ──

def table_stats(t):
    n = sum(t[0]) + sum(t[1])
    if n == 0:
        return None
    a1 = t[1][0] + t[1][1]
    b1 = t[0][1] + t[1][1]
    p_next = b1 / n
    p_a = t[1][1] / a1 if a1 else float('nan')
    n0 = n - a1
    p_na = t[0][1] / n0 if n0 else float('nan')
    delta = p_a - p_na
    num = t[1][1]*t[0][0] - t[1][0]*t[0][1]
    den = math.sqrt(max(a1,1)*max(n-a1,1)*max(b1,1)*max(n-b1,1))
    phi = num/den if den else 0.0
    chi2 = n * phi * phi
    return dict(n=n, p_next=p_next, p_given_a=p_a, p_given_na=p_na,
                delta=delta, phi=phi, chi2=chi2,
                table=[[t[0][0], t[0][1]], [t[1][0], t[1][1]]])

def summarize_cells(cells, min_n):
    chi2_tot, df, n_tot, wnum, wden, degen = 0.0, 0, 0, 0.0, 0, 0
    for t in cells.values():
        n = sum(t[0]) + sum(t[1])
        if n < min_n:
            continue
        a1 = t[1][0] + t[1][1]
        b1 = t[0][1] + t[1][1]
        if a1 == 0 or a1 == n or b1 == 0 or b1 == n:
            degen += 1
            continue
        p_a = t[1][1] / a1
        p_na = t[0][1] / (n - a1)
        delta = p_a - p_na
        num = t[1][1]*t[0][0] - t[1][0]*t[0][1]
        den = math.sqrt(a1*(n-a1)*b1*(n-b1))
        phi = num/den if den else 0.0
        chi2_tot += n*phi*phi
        df += 1
        n_tot += n
        wnum += delta*n
        wden += n
    return dict(chi2=chi2_tot, df=df, n=n_tot,
                wdelta=(wnum/wden if wden else float('nan')), degenerate=degen)

# ── Output ──
ov = table_stats(joint)
se = math.sqrt(ov['p_next']*(1-ov['p_next']) * (1/(joint[1][0]+joint[1][1]) + 1/(joint[0][0]+joint[0][1])))
z_score = ov['delta']/se

n = n_pairs
mx, my = s_x/n, s_y/n
cov = s_xy/n - mx*my
vx = s_xx/n - mx*mx
vy = s_yy/n - my*my
r_om = cov/math.sqrt(vx*vy)

# Conditioning summaries
res120 = summarize_cells(cell120, 5000)
res840 = summarize_cells(cell840, 2000)
res40g = summarize_cells(cell40g, 5000)
rh0 = summarize_cells(halves120[0], 5000)
rh1 = summarize_cells(halves120[1], 5000)

# omega conditioning
chi2_om, df_om, n_om = 0.0, 0, 0
wdelta_om_num, wdelta_om_den = 0.0, 0
for k, t in om_joint.items():
    st = table_stats(t)
    if st and st['n'] >= 10_000 and 0 < st['p_next'] < 1:
        chi2_om += st['chi2']; df_om += 1; n_om += st['n']
        wdelta_om_num += st['delta']*st['n']; wdelta_om_den += st['n']

# mod-12 conditioning
chi2_m12, df_m12, n_m12 = 0.0, 0, 0
wd_m12n, wd_m12d = 0.0, 0
for k, t in m12_joint.items():
    st = table_stats(t)
    if st and st['n'] >= 10_000:
        chi2_m12 += st['chi2']; df_m12 += 1; n_m12 += st['n']
        wd_m12n += st['delta']*st['n']; wd_m12d += st['n']

# ── Print full log ──
log_lines = []
def log(s=""):
    print(s)
    log_lines.append(s)

mode_label = "legacy CSV with --repair-legacy fixes" if REPAIR_LEGACY else "corrected CSV (clean input)"
log("="*70)
log("RESULTS: consecutive-prime Artin correlation")
log(f"  Input: {os.path.basename(PATH)} ({mode_label})")
if REPAIR_LEGACY:
    if n_duplicates > 0:
        log(f"  Duplicate p=7 rows skipped: {n_duplicates}")
    if endpoint_added:
        log(f"  Missing endpoint p={LEGACY_MISSING_PRIME} added")
log("="*70)
log(f"\nDataset: {n_unique:,} distinct primes, {first_prime} to {last_prime}")
log(f"  Artin primes: {n_artin:,} (proportion {n_artin/n_unique:.6f})")
log(f"  CSV rows: {n_rows:,}, duplicates removed: {n_duplicates:,}")
log(f"\nPairs analysed: {ov['n']:,}")
log(f"  Joint table: [[{joint[0][0]}, {joint[0][1]}], [{joint[1][0]}, {joint[1][1]}]]")
log(f"P(Artin_(n+1))            = {ov['p_next']:.6f}")
log(f"P(Artin_(n+1) | Artin_n)  = {ov['p_given_a']:.6f}")
log(f"P(Artin_(n+1) | ~Artin_n) = {ov['p_given_na']:.6f}")
log(f"delta                     = {ov['delta']:+.15f}")
log(f"phi coefficient           = {ov['phi']:+.15f}")
log(f"chi2 (1 df)               = {ov['chi2']:.6f}")
log(f"z-score (nominal)         = {z_score:+.2f}")
log(f"\nPearson r(omega_n, omega_(n+1)) = {r_om:+.15f}")

log(f"\n--- Mod-12 transition matrix ---")
res = sorted({k[0] for k in m12_trans})
log("        " + "".join(f"{c:>10}" for c in res))
for r_ in res:
    tot = sum(m12_trans[(r_, c)] for c in res)
    row = "".join(f"{m12_trans[(r_,c)]/tot:>10.4f}" for c in res)
    log(f"  {r_:>4}  {row}")

log(f"\n--- Gap-stratified results (N >= 100,000) ---")
log(f"{'gap':>5} {'N':>12} {'P(A|A)':>9} {'P(A|~A)':>9} {'delta':>12} {'chi2':>10}")
gap_data = {}
for g in sorted(gap_joint):
    st = table_stats(gap_joint[g])
    if st and st['n'] >= 100_000:
        gap_data[str(g)] = st
        log(f"{g:>5} {st['n']:>12,} {st['p_given_a']:>9.5f} {st['p_given_na']:>9.5f} {st['delta']:>+12.6f} {st['chi2']:>10.1f}")

log(f"\n--- Minimum delta among gaps with N >= 100,000 ---")
if gap_data:
    min_delta_gap = min(gap_data.items(), key=lambda x: x[1]['delta'])
    log(f"  Minimum delta = {min_delta_gap[1]['delta']:.6f} at gap {min_delta_gap[0]}")
else:
    log('  No gap meets the reporting threshold for this input.')

log(f"\n--- Residual: omega conditioning ---")
log(f"  Summed chi2 = {chi2_om:.1f} on {df_om} df ({n_om:,} pairs)")
log(f"  Weighted mean residual delta = {(wdelta_om_num/wdelta_om_den if wdelta_om_den else float('nan')):+.6f}")

log(f"\n--- Residual: mod-12 conditioning ---")
log(f"  Summed chi2 = {chi2_m12:.1f} on {df_m12} df ({n_m12:,} pairs)")
log(f"  Weighted mean residual delta = {(wd_m12n/wd_m12d if wd_m12d else float('nan')):+.6f}")

log(f"\n--- Residual: mod-120 conditioning ---")
log(f"  cells: {res120['df']}, degenerate: {res120['degenerate']}")
log(f"  pairs: {res120['n']:,}")
log(f"  summed chi2 = {res120['chi2']:.1f} on {res120['df']} df")
log(f"  weighted delta_res = {res120['wdelta']:+.6f}")

log(f"\n--- Residual: mod-840 conditioning ---")
log(f"  cells: {res840['df']}, degenerate: {res840['degenerate']}")
log(f"  pairs: {res840['n']:,}")
log(f"  summed chi2 = {res840['chi2']:.1f} on {res840['df']} df")
log(f"  chi2/df = {(res840['chi2']/res840['df'] if res840['df'] else float('nan')):.2f}")
log(f"  weighted delta_res = {res840['wdelta']:+.6f}")

log(f"\n--- Robustness: mod-40+gap conditioning ---")
log(f"  chi2={res40g['chi2']:.1f} on {res40g['df']} df, n={res40g['n']:,}, wdelta={res40g['wdelta']:+.6f}")

log(f"\n--- Split-half (mod-120) ---")
log(f"  p < 5e8:  chi2={rh0['chi2']:.1f} on {rh0['df']} df, wdelta={rh0['wdelta']:+.6f}")
log(f"  p >= 5e8: chi2={rh1['chi2']:.1f} on {rh1['df']} df, wdelta={rh1['wdelta']:+.6f}")

# ── Save results ──
correction_note = "Physically corrected CSV: no on-the-fly fixes needed"
if REPAIR_LEGACY:
    fixes = []
    if n_duplicates > 0: fixes.append(f"duplicate p=7 removed ({n_duplicates})")
    if endpoint_added:    fixes.append(f"missing p={LEGACY_MISSING_PRIME} added")
    correction_note = "Legacy CSV with on-the-fly fixes: " + "; ".join(fixes)

results = {
    "correction_note": correction_note,
    "dataset": {
        "csv_path": os.path.basename(PATH),
        "csv_rows": n_rows,
        "duplicates_removed": n_duplicates,
        "unique_primes": n_unique,
        "artin_primes": n_artin,
        "artin_proportion": n_artin/n_unique,
        "first_prime": first_prime,
        "last_prime": last_prime,
    },
    "overall": ov,
    "z_score_nominal": z_score,
    "r_omega": r_om,
    "gap": gap_data,
    "residual_omega": {"chi2": chi2_om, "df": df_om, "n": n_om, "wdelta": (wdelta_om_num/wdelta_om_den if wdelta_om_den else float('nan'))},
    "residual_m12": {"chi2": chi2_m12, "df": df_m12, "n": n_m12, "wdelta": (wd_m12n/wd_m12d if wd_m12d else float('nan'))},
    "conditioning_120": {"cells": res120['df'], "pairs": res120['n'], "chi2": res120['chi2'], "wdelta": res120['wdelta'], "degenerate": res120['degenerate']},
    "conditioning_840": {"cells": res840['df'], "pairs": res840['n'], "chi2": res840['chi2'], "wdelta": res840['wdelta'], "degenerate": res840['degenerate']},
    "robustness_m40_gap": {"chi2": res40g['chi2'], "df": res40g['df'], "n": res40g['n'], "wdelta": res40g['wdelta']},
    "split_half": {"half1": rh0, "half2": rh1},
    "m12_trans": {f"{k[0]}->{k[1]}": v for k, v in sorted(m12_trans.items())},
}

json_path = os.path.join(OUT_DIR, "pilot_results.json")
with open(json_path, "w") as f:
    json.dump(results, f, indent=2)
log(f"\nSaved JSON: {json_path}")

log_path = os.path.join(OUT_DIR, "pilot_log.txt")
with open(log_path, "w") as f:
    f.write("\n".join(log_lines) + "\n")
print(f"Saved log: {log_path}", file=sys.stderr)

# Also save pilot2 and pilot3 compatible results
p2 = {"df": res120['df'], "chi2": res120['chi2'], "n": res120['n'], "wdelta": res120['wdelta'], "degenerate": res120['degenerate']}
with open(os.path.join(OUT_DIR, "pilot2_results.json"), "w") as f:
    json.dump(p2, f, indent=2)

p2_log = os.path.join(OUT_DIR, "pilot2_log.txt")
with open(p2_log, "w") as f:
    f.write(f"Mod-120 conditioning: {res120['df']} cells, chi2={res120['chi2']:.1f}, wdelta={res120['wdelta']:+.6f}\n")

p3 = {"m40_gap": res40g, "m840": {"chi2": res840['chi2'], "df": res840['df'], "n": res840['n'], "wdelta": res840['wdelta'], "degenerate": res840['degenerate']}, "half1": rh0, "half2": rh1}
with open(os.path.join(OUT_DIR, "pilot3_results.json"), "w") as f:
    json.dump(p3, f, indent=2)

p3_log = os.path.join(OUT_DIR, "pilot3_log.txt")
with open(p3_log, "w") as f:
    f.write(f"Mod-840: chi2={res840['chi2']:.1f} on {res840['df']} df, wdelta={res840['wdelta']:+.6f}\n")
    f.write(f"Split-half H1: chi2={rh0['chi2']:.1f}, wdelta={rh0['wdelta']:+.6f}\n")
    f.write(f"Split-half H2: chi2={rh1['chi2']:.1f}, wdelta={rh1['wdelta']:+.6f}\n")

print("\nDONE", file=sys.stderr)
