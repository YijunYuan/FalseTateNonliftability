/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Mathlib
public import FalseTateNonliftability.LaurentSeries
public import FalseTateNonliftability.PowerSeries
public import FalseTateNonliftability.Differential
public import FalseTateNonliftability.CoefficientRing
public import FalseTateNonliftability.Liftability
public import FalseTateNonliftability.FalseTate

/-!
# Non-liftability of the field of norms of the `p`-adic false Tate curve extension

This library formalizes Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate
curve extension*. Let `p ≥ 3` be a prime and `ℚ_p^FT = ℚ_p(p^{1/p^∞}, ζ_{p^∞})` the false Tate
curve extension, with field of norms `X = X_{ℚ_p}(ℚ_p^FT)` and residue field `𝔽_p`. For every
finite totally ramified extension `F/ℚ_p`, the action of `Gal(ℚ_p^FT/ℚ_p)` on `X` is not
`F`-liftable in the sense of Berger (Theorem A), and the obstruction already occurs modulo
`𝔪_F ^ (e + 1)`, where `e = v_F(p)`, for lifts of `T^p` and of the coordinate series of the
Kummer generator `τ` and of the tame generator `δ` alone (Proposition 1.3).

The library has seven layers, each with an aggregate module imported here: `Mathlib` (upstream
candidates), `LaurentSeries` (substitution, §2.1, and §3), `PowerSeries` (principal units, §4.2),
`Differential` (§4), `CoefficientRing` (the ring `A_K`, §2.2, Theorem 3.1 and §6), `Liftability`
(Definition 1.1, Lemma 2.2, Proposition 2.3) and `FalseTate` (§5, Proposition 1.3, Theorem A).
All declarations below are in the namespace `FalseTateNonliftability` unless they start with
`LaurentSeries.` or `PowerSeries.`.

## Main definitions

* Yuan, Definition 1.1 (Berger 2014): `IsLiftable p K L F`, the action of `Gal(L/K)` on `X_K(L)`
  is `F`-liftable (`Liftability/IsLiftable`). It is the existence of a lift
  `CoordinateFamily.Lift`, `CoordinateFamily.Liftable` (`Liftability/Defs`) of the coordinate
  family `IsLiftable.coordinateFamily` of the action in a uniformizer to the ring `A_K`, which is
  `CoefficientRing O` for `O = 𝒪_F`, a complete discrete valuation ring with residue field
  `κ((T))` (`CoefficientRing.isDiscreteValuationRing`, `CoefficientRing.isAdicComplete`,
  `CoefficientRing.residueFieldEquiv`, in `CoefficientRing/Truncation`). Finite lifts modulo
  `𝔪_F ^ (r + 1)` on a subset of the group are `CoordinateFamily.FiniteLift` and
  `CoordinateFamily.FiniteLiftable`.
* Yuan, Definition 2.5: `Truncation.derivativeLevel` and `Truncation.normalizedDerivative`, the
  derivative level `s(P)` and the normalized derivative `h_P`
  (`CoefficientRing/NormalizedDerivative`), built from the layers `Truncation.layer j X = ϖ⁻ʲX`
  (`CoefficientRing/Truncation`).
* Yuan, Lemma 1.2 (3): `tameGenerator`, notation `δ`, with `padicCyclotomicCharacter_tameGenerator`
  and `orderOf_map_toZMod_padicCyclotomicCharacter_tameGenerator` (`FalseTate/TameGenerator`); the
  Kummer generator `τ` is `FalseTateExtension.kummerGenerator`. Lemma 1.2 (1), (2) are in
  FalseTateExtension.

## Main results

* Yuan, Theorem A: `not_isLiftable_falseTate` (for `ℚ_p^FT`) and
  `not_isLiftable_falseTateExtension` (for `ℚ_p(π^{1/p^∞}, ζ_{p^∞})` and any uniformizer `π` of
  `ℚ_p`), in `FalseTate/Main`.
* Yuan, Proposition 1.3: `not_finiteLiftable_falseTate` and
  `not_finiteLiftable_falseTateExtension` (`FalseTate/Main`). The abstract form over a discrete
  valuation ring is `Truncation.false_of_commute` (`CoefficientRing/Obstruction`). Over
  `F = ℚ_p`, the Kummer generator alone has no lift modulo `p ^ 2` commuting with a lift of
  Frobenius: `not_finiteLiftable_kummerGenerator_bot` (`FalseTate/Main`).
* Yuan, Proposition 2.3: `isLiftable_iff_uniformizer`, `isLiftable_iff_exists_uniformizer`,
  `isLiftable_iff_forall_uniformizer`, `IsLiftable.liftable_coordinateFamily_iff` and
  `IsLiftable.finiteLiftable_coordinateFamily_iff` (`Liftability/IsLiftable`); for an abstract
  coordinate family and a change of variable, `CoordinateFamily.liftable_conj_iff` and
  `CoordinateFamily.finiteLiftable_conj_iff` (`Liftability/CoordinateChange`).

## The other numbered results

* Lemma 2.1: `LaurentSeries.subst`, `LaurentSeries.subst_unique` (1),
  `LaurentSeries.subst_comp_subst`, `LaurentSeries.derivative_subst` (2),
  `LaurentSeries.substEquiv_symm` (3) (`LaurentSeries/Substitution`), `PowerSeries.map_compInv`
  (3) (`Mathlib/RingTheory/PowerSeries/Composition`); over `A_K`: `CoefficientRing.subst_X`,
  `CoefficientRing.subst_unique`, `CoefficientRing.subst_comp_subst`
  (`CoefficientRing/Substitution`).
* Lemma 2.2: `FieldOfNorms.coordinateSeries`, `FieldOfNorms.coordinateFamily`;
  `FieldOfNorms.isUnit_coeff_one_coordinateSeries` (1), `FieldOfNorms.aut_laurentEquiv` (2),
  `FieldOfNorms.coordinateSeries_mul` (3), `FieldOfNorms.coordinateSeries_eq_conj` (4)
  (`Liftability/FieldOfNorms`).
* Lemma 2.4: `Truncation.derivativeLevel_eq_iff`, `Truncation.one_le_derivativeLevel`;
  `Truncation.subst_normalizedDerivative_of_commute` (1); `Truncation.derivativeLevel_conj`,
  `Truncation.subst_normalizedDerivative_conj`, `Truncation.order_normalizedDerivative_conj` (2);
  `Truncation.exists_normalizedDerivative_eq_derivative`,
  `Truncation.exists_normalizedDerivative_eq_single_add_derivative`,
  `Truncation.order_derivative_normalizedDerivative_le` (3)
  (`CoefficientRing/NormalizedDerivative`).
* Theorem 3.1: `Truncation.order_normalizedDerivative_le`, with the series computation
  `LaurentSeries.order_le_of_subst_eq_derivative_pow_mul` (`CoefficientRing/NormalizedDerivative`).
* Lemma 3.2: `LaurentSeries.subst_sub_mem_orderAddSubgroup`,
  `LaurentSeries.subst_sub_leadingTerm_mem` (`LaurentSeries/Taylor`).
* Lemma 3.3: `PowerSeries.ramificationNumber_iterate_eq_of_resonant` (`LaurentSeries/NormalForm`).
* Theorem 3.4: `PowerSeries.exists_normalForm` (`LaurentSeries/NormalForm`).
* Lemma 4.1: `LaurentSeries.exists_exact_invariant_of_weighted_identities`
  (`Differential/InvariantExactDifferential`).
* Lemma 4.2: `LaurentSeries.padic_limit_order_eq_zero_of_approximate_invariance`
  (`Differential/ApproximateInvariants`), with the rigidity
  `PowerSeries.eq_zero_of_principalUnitPow_mul_subst_eq` (`PowerSeries/UnitRigidity`).
* Proposition 4.3: `LaurentSeries.padic_ramification_limit_eq_of_invariant_exact_differential`
  (`Differential/ExactDifferentialLimit`).
* Proposition 5.1: `ramificationNumber_kummerGenerator_pow` (5.1),
  `kummerRamificationBreak_tendsto_atTop`, `kummerRamificationBreak_tendsto_padic` (5.2) and
  `kummerRamificationLimit_notMem_range_intCast` (`FalseTate/RamificationNumbers`); the
  congruence and growth of (1) are `FalseTateExtension.kummerRamificationBreak_succ_dvd` and
  `FalseTateExtension.kummerRamificationBreak_growth`; all of it as used in §6:
  `hasRamificationLimit_coordinateFamily_series_kummerGenerator` (`FalseTate/Main`).
* Lemma 5.3: `coeff_one_coordinateSeries_tameGenerator`,
  `orderOf_coeff_one_coordinateSeries_tameGenerator` (`FalseTate/TameGenerator`).
* §6, case 1 (`s(P) = e` is impossible): `Truncation.derivativeLevel_lt_absoluteRamificationIdx`;
  case 2 (`s(P) < e` is impossible): `Truncation.absoluteRamificationIdx_le_derivativeLevel`
  (`CoefficientRing/Obstruction`).

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38
  (Definition 1.1 in Yuan).
* J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Ann. Sci. ENS 16 (1983), 59–89, Proposition 3.3.2.
* F. Viviani, *Ramification groups and Artin conductors of radical extensions of ℚ*, J. Théor.
  Nombres Bordeaux 16 (2004), 779–816, Corollary 6.10.
* J.-P. Serre, *Local Fields*, Chapter IV.
-/
