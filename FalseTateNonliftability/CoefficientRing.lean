/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative
public import FalseTateNonliftability.CoefficientRing.Obstruction
public import FalseTateNonliftability.CoefficientRing.Substitution
public import FalseTateNonliftability.CoefficientRing.Truncation

/-!
# The coefficient ring, the normalized derivative and the two obstructions

Let `O` be a discrete valuation ring with maximal ideal `𝔪`, uniformizer `ϖ` and residue field
`κ`; in Yuan, `O` is the ring of integers of a finite extension `F` of `ℚ_p`. This layer
constructs the coefficient ring `A` of Definition 1.1, the `𝔪`-adic completion of `O((T))`, its
truncations `R_r = (O ⧸ 𝔪 ^ (r + 1))((T))`, substitution in `A` (Lemma 2.1 over `A`) and the
coordinate changes `P ↦ H ∘ P ∘ H^{∘-1}` used in Proposition 2.3. For `κ = 𝔽_p` and `e = v_ϖ(p)`,
it defines the derivative level `s(P)` and the normalized derivative `h_P = ϖ⁻ˢ P'` of a lift
`P ∈ R_e` of `T ^ p` (Definition 2.5), proves Lemma 2.4 and Proposition 3.1, and combines them with
§3 and §4 into the two cases of the proof of Proposition 1.4 in §6.

## Main definitions

* `FalseTateNonliftability.CoefficientRing O`: the ring `A` (Yuan, Definition 1.1).
* `FalseTateNonliftability.Truncation O r`: the truncation `O ⧸ 𝔪 ^ (r + 1)`.
* `FalseTateNonliftability.Truncation.layer j X`: the series `ϖ⁻ʲ X ∈ κ((T))` (Yuan, §2.2).
* `FalseTateNonliftability.CoefficientRing.subst G`: substitution `f ↦ f(G)` in `A`.
* `LaurentSeries.conj H P`, `FalseTateNonliftability.CoefficientRing.conj H P`: the conjugate
  `H ∘ P ∘ H^{∘-1}`.
* `FalseTateNonliftability.Truncation.derivativeLevel P`,
  `FalseTateNonliftability.Truncation.normalizedDerivative P`: `s(P)` and `h_P`
  (Yuan, Definition 2.5).

## Main results

* Yuan, Lemma 2.4: `FalseTateNonliftability.Truncation.subst_normalizedDerivative_of_commute`
  (1), `FalseTateNonliftability.Truncation.subst_normalizedDerivative_conj` (2),
  `FalseTateNonliftability.Truncation.exists_normalizedDerivative_eq_derivative` and
  `FalseTateNonliftability.Truncation.exists_normalizedDerivative_eq_single_add_derivative` (3)
  (`CoefficientRing/NormalizedDerivative`).
* Yuan, Proposition 3.1: `FalseTateNonliftability.Truncation.order_normalizedDerivative_le`
  (`CoefficientRing/NormalizedDerivative`).
* Yuan, §6, case 1 (`s(P) = e` is impossible):
  `FalseTateNonliftability.Truncation.derivativeLevel_lt_absoluteRamificationIdx`; case 2
  (`s(P) < e` is impossible):
  `FalseTateNonliftability.Truncation.absoluteRamificationIdx_le_derivativeLevel`; together:
  `FalseTateNonliftability.Truncation.false_of_commute` (`CoefficientRing/Obstruction`).

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Definition 1.1, §2, Proposition 3.1 and §6.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/
