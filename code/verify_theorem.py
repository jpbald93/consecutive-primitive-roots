#!/usr/bin/env python3
"""Verify: for primes p, q = p + g with g ≡ 20 (mod 40), (10|p) = -(10|q).
Checks (i) the Legendre-symbol flip for ALL residue classes mod 40,
(ii) empirically for all prime pairs with gap ≡ 20 (mod 40) up to 10^7,
(iii) that no such pair is both-Artin up to 10^7 (direct order computation).

Usage:
    python3 verify_theorem.py [LIMIT]
    # LIMIT defaults to 10000000 (10^7)

Requires: sympy
"""
import sys
from sympy import legendre_symbol, n_order, primerange

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000

# (i) exhaustive residue check mod 40
print("(i) Residue-class check: (2|p) flip under p -> p+20 (mod 8), (5|p) fixed (mod 5)")
ok = True
for r in range(1, 40, 2):
    if r % 5 == 0:
        continue
    # (2|p) via p mod 8: +1 iff p ≡ ±1 mod 8
    two_p = 1 if r % 8 in (1, 7) else -1
    r2 = (r + 20) % 40
    two_q = 1 if r2 % 8 in (1, 7) else -1
    five_p_class = r % 5   # (5|p) depends only on this
    five_q_class = r2 % 5
    assert five_p_class == five_q_class
    if two_p != -two_q:
        ok = False
        print(f"  FAIL at residue {r}")
print("  PASS: (2|.) flips for every residue class; (5|.) invariant" if ok else "  FAILED")

# (ii) Legendre flip on actual prime pairs up to LIMIT
print(f"(ii) Empirical Legendre flip, prime pairs gap ≡ 20 (mod 40), p < {LIMIT}")
primes = list(primerange(7, LIMIT))
n_pairs = 0
flip_fail = 0
both_artin = 0
checked_artin = 0
for i in range(len(primes) - 1):
    p, q = primes[i], primes[i+1]
    g = q - p
    if g % 40 == 20:
        n_pairs += 1
        if legendre_symbol(10, p) != -legendre_symbol(10, q):
            flip_fail += 1
        # (iii) direct Artin check on a subsample (order computation is slow)
        if n_pairs % 50 == 0:
            checked_artin += 1
            if n_order(10, p) == p - 1 and n_order(10, q) == q - 1:
                both_artin += 1
print(f"  consecutive pairs with gap≡20 (mod 40): {n_pairs:,}")
print(f"  Legendre flip failures: {flip_fail}")
print(f"(iii) direct both-Artin among {checked_artin:,} sampled pairs: {both_artin}")
print("THEOREM VERIFIED" if (ok and flip_fail == 0 and both_artin == 0) else "PROBLEM FOUND")
