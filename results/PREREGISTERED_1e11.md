# Pre-registered prediction for delta(10^11) — written BEFORE the run

Timestamp: 2026-09-11 ~16:17 ET. Recorded before launching the 10^11 census so
the comparison is a genuine prediction, not a post-hoc fit.

Measured so far:
  delta(1e8)  = -0.013360
  delta(1e9)  = -0.014140158840
  delta(1e10) = -0.014723292716

Increments: -0.000780 (1e8->1e9), -0.000583 (1e9->1e10). Ratio r = 0.747.

## Three competing models and what each predicts

| model | predicted delta(1e11) |
|---|---|
| geometric decay of increments (r = 0.747) | **-0.015159** |
| linear in log x (constant increment)      | -0.015306 |
| delta -> 0 (separable-channel heuristic)  | LESS negative than -0.014723 |

Sampling SE on delta at 1e11 is ~1.6e-5. The models are separated by ~4e-4,
about 25-28 SE, so the run discriminates them decisively. This is not a
noise-limited question.

## What I will conclude

- If delta(1e11) is near -0.0152: geometric/convergent picture supported;
  extrapolated limit ~ -0.0165. Persistence Conjecture strongly supported.
- If near -0.0153: closer to linear-in-log; no finite limit visible yet;
  Persistence supported but no limit claim.
- If less negative than -0.014723: the trend has REVERSED and the
  delta -> 0 branch is live. This would be the interesting outcome and would
  require reporting against the current framing.

Nothing about the theorem (zero doubly-Artin at gaps 20/60) is in question;
that is proved. Only the asymptotic behaviour of delta is at stake.
