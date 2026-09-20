#!/usr/bin/env python3
"""
stitch_audit.py — combine the sharded output of independent_audit_1e9.c into
the global Paper 1 census, and compare against the published values.

The shards partition [7, 10^9] into consecutive disjoint ranges. Each shard
counts consecutive-prime PAIRS wholly inside its own range, so the pairs that
straddle a shard boundary (last prime of shard k, first prime of shard k+1)
are missing from every shard and must be added back here. That is the only
non-additive part of the stitch.

Usage:
    python3 stitch_audit.py shard_*.json
    python3 stitch_audit.py --dir /path/to/shards
"""
import json, sys, glob, os, math

PUBLISHED = {
    "n_primes":  50847531,      # primes counted (p >= 7, p != 5)
    "n_artin":   19016617,      # Artin primes base 10
    "n_pairs":   50847530,      # consecutive pairs
    "table":     [[19758045, 12072868], [12072869, 6943748]],
    "delta":     -0.014140158839795136,
    "chi2":      10166.663432261103,
    "g2060_pairs": 2195882,
    "g2060_both":  0,
}

def load(paths):
    rows = []
    for p in sorted(paths):
        txt = open(p).read().strip()
        if not txt:
            raise SystemExit(f"empty shard: {p}")
        rows.append(json.loads(txt))
    rows.sort(key=lambda r: r["lo"])
    return rows

def main():
    args = sys.argv[1:]
    if args and args[0] == "--dir":
        paths = glob.glob(os.path.join(args[1], "shard_*.json"))
    else:
        paths = args or glob.glob("shard_*.json")
    rows = load(paths)

    # contiguity check: ranges must tile [7, 1e9] with no gap or overlap
    for a, b in zip(rows, rows[1:]):
        if a["hi"] + 1 != b["lo"]:
            raise SystemExit(f"non-contiguous: {a['hi']} then {b['lo']}")

    n_primes = sum(r["n_primes"] for r in rows)
    n_artin  = sum(r["n_artin"]  for r in rows)
    t = [[0, 0], [0, 0]]
    for r in rows:
        t[0][0] += r["t00"]; t[0][1] += r["t01"]
        t[1][0] += r["t10"]; t[1][1] += r["t11"]
    g_pairs = sum(r["g2060_pairs"] for r in rows)
    g_both  = sum(r["g2060_both"]  for r in rows)

    # stitch the boundary pairs
    boundary = 0
    for a, b in zip(rows, rows[1:]):
        if a["last_p"] and b["first_p"]:
            t[a["last_a"]][b["first_a"]] += 1
            boundary += 1
            g = b["first_p"] - a["last_p"]
            if g in (20, 60):
                g_pairs += 1
                if a["last_a"] and b["first_a"]:
                    g_both += 1

    n_pairs = t[0][0] + t[0][1] + t[1][0] + t[1][1]

    # delta = P(Artin(p_{n+1}) | Artin(p_n)) - P(Artin(p_{n+1}) | not Artin(p_n))
    n1 = t[1][0] + t[1][1]
    n0 = t[0][0] + t[0][1]
    delta = t[1][1] / n1 - t[0][1] / n0

    # Pearson chi-square on the 2x2 table
    row = [n0, n1]
    col = [t[0][0] + t[1][0], t[0][1] + t[1][1]]
    chi2 = 0.0
    for i in (0, 1):
        for j in (0, 1):
            e = row[i] * col[j] / n_pairs
            chi2 += (t[i][j] - e) ** 2 / e

    got = {
        "n_primes": n_primes, "n_artin": n_artin, "n_pairs": n_pairs,
        "table": t, "delta": delta, "chi2": chi2,
        "g2060_pairs": g_pairs, "g2060_both": g_both,
    }

    print(f"shards: {len(rows)}   boundary pairs stitched: {boundary}")
    print()
    print(f"{'quantity':<16} {'independent':>22} {'published':>22}  match")
    ok = True
    for k in ("n_primes", "n_artin", "n_pairs", "g2060_pairs", "g2060_both"):
        g, p = got[k], PUBLISHED[k]
        m = (g == p); ok &= m
        print(f"{k:<16} {g:>22,} {p:>22,}  {'OK' if m else 'MISMATCH'}")
    m = got["table"] == PUBLISHED["table"]; ok &= m
    print(f"{'table':<16} {str(got['table']):>22} {str(PUBLISHED['table']):>22}  {'OK' if m else 'MISMATCH'}")
    for k, tol in (("delta", 1e-12), ("chi2", 1e-6)):
        g, p = got[k], PUBLISHED[k]
        m = abs(g - p) < tol; ok &= m
        print(f"{k:<16} {g:>22.12f} {p:>22.12f}  {'OK' if m else 'MISMATCH'}")
    print()
    print("INDEPENDENT AUDIT: " + ("PASS — published census reproduced exactly"
                                   if ok else "FAIL — see mismatches above"))
    json.dump(got, open("independent_audit_result.json", "w"), indent=2)
    print("wrote independent_audit_result.json")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
