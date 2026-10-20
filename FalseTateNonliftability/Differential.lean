/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Differential.ApproximateInvariants
public import FalseTateNonliftability.Differential.ExactDifferentialLimit
public import FalseTateNonliftability.Differential.InvariantExactDifferential

/-!
# Invariant exact differentials

Let `κ` be a finite field of characteristic `p`, let `f ∈ T + T ^ 2 κ⟦T⟧`, and let
`σ : x ↦ x(f)` be the corresponding automorphism of `κ((T))`, acting on differentials by
`σ(a dT) = a(f) f' dT`. This layer contains the obstruction of Yuan, §4, to lifts of Frobenius of
derivative level `s(P) < e`. If the normalized derivative `h_P = A'` of such a lift satisfies the
weighted identities of Lemma 2.4 (1) for `f` and for a series `g` whose linear coefficient has
order `p - 1`, then `σ` fixes a nonzero exact differential `ω` (Lemma 4.1). If `σ` has infinite
order, the valuations of approximate invariants of `σ` have `p`-adic limit `0` (Lemma 4.2), and
consequently the `p`-adic limit of the ramification numbers `i(σ ^ (p ^ n))` is the integer
`-ord_T(ω) - 1` (Proposition 4.3).

## Main results

* `LaurentSeries.exists_exact_invariant_of_weighted_identities`: Yuan, Lemma 4.1
  (`Differential/InvariantExactDifferential`).
* `LaurentSeries.padic_limit_order_eq_zero_of_approximate_invariance`: Yuan, Lemma 4.2
  (`Differential/ApproximateInvariants`).
* `LaurentSeries.padic_ramification_limit_eq_of_invariant_exact_differential`: Yuan,
  Proposition 4.3 (`Differential/ExactDifferentialLimit`).

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*, §4.
-/
