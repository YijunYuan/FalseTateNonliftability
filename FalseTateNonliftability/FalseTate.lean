/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.FalseTate.Main
public import FalseTateNonliftability.FalseTate.RamificationNumbers
public import FalseTateNonliftability.FalseTate.TameGenerator

/-!
# The false Tate curve extension

The arithmetic of the false Tate curve extension `K_FT = ℚ_p(π^{1/p^∞}, ζ_{p^∞})` of `ℚ_p` that
enters the proof of Theorem A, and the proof itself. The ramification numbers of the iterates
`τ^{p^k}` of the Kummer generator on the field of norms `X_{ℚ_p}(K_FT)` are
`d_k = (2 p^{2k+2} + p - 1)/(p + 1)`, which tend to `∞` and to `(p - 1)/(p + 1) ∉ ℤ` in `ℤ_p`
(Yuan, Proposition 5.1). The linear coefficient of the coordinate series of the tame generator
`δ` has multiplicative order `p - 1` (Yuan, Lemma 5.3). Together with the obstructions of Yuan, §6
these give Proposition 1.4 and Theorem A.

## Main definitions

* `FalseTateNonliftability.kummerRamificationLimit`: `(p - 1)/(p + 1) ∈ ℤ_p`
  (`FalseTate/RamificationNumbers`).
* `FalseTateNonliftability.tameGenerator`, notation `δ` (`FalseTate/TameGenerator`).

## Main results

* `FalseTateNonliftability.ramificationNumber_kummerGenerator_pow`,
  `FalseTateNonliftability.kummerRamificationBreak_tendsto_padic`: Yuan, Proposition 5.1
  (`FalseTate/RamificationNumbers`).
* `FalseTateNonliftability.tameGenerator_mul_kummerGenerator`: `δ τ = τ^{χ(δ)} δ` (Yuan,
  Lemma 1.3 (3), `FalseTate/TameGenerator`).
* `FalseTateNonliftability.orderOf_coeff_one_coordinateSeries_tameGenerator`: Yuan, Lemma 5.3
  (`FalseTate/TameGenerator`).
* `FalseTateNonliftability.not_finiteLiftable_falseTate`: Yuan, Proposition 1.4
  (`FalseTate/Main`).
* `FalseTateNonliftability.not_isLiftable_falseTate`: Yuan, Theorem A (`FalseTate/Main`).

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Proposition 1.4, Proposition 5.1, Lemma 5.3, §6 and Theorem A.
-/
