/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Mathlib
public import FalseTateNonliftability.LaurentSeries.Admissible
public import FalseTateNonliftability.LaurentSeries.ApproximateInvariants
public import FalseTateNonliftability.LaurentSeries.CharacteristicP
public import FalseTateNonliftability.LaurentSeries.CoefficientMap
public import FalseTateNonliftability.LaurentSeries.Derivative
public import FalseTateNonliftability.LaurentSeries.Evaluation
public import FalseTateNonliftability.LaurentSeries.EvaluationContinuity
public import FalseTateNonliftability.LaurentSeries.ExactDifferentialLimit
public import FalseTateNonliftability.LaurentSeries.FrobeniusKernel
public import FalseTateNonliftability.LaurentSeries.InvariantExactDifferential
public import FalseTateNonliftability.LaurentSeries.IterateGrowth
public import FalseTateNonliftability.LaurentSeries.NilpotentPower
public import FalseTateNonliftability.LaurentSeries.NormalForm
public import FalseTateNonliftability.LaurentSeries.OrderTopology
public import FalseTateNonliftability.LaurentSeries.PowerSeriesEval
public import FalseTateNonliftability.LaurentSeries.PrimitiveNormalization
public import FalseTateNonliftability.LaurentSeries.PrincipalQuotient
public import FalseTateNonliftability.LaurentSeries.Substitution
public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.LaurentSeries.TruncationDensity
public import FalseTateNonliftability.PowerSeries.PrincipalUnitIntegerPowers
public import FalseTateNonliftability.PowerSeries.PrincipalUnitPowers
public import FalseTateNonliftability.PowerSeries.UnitCompactness
public import FalseTateNonliftability.PowerSeries.UnitRigidity
public import FalseTateNonliftability.CoefficientRing.CoordinateChange
public import FalseTateNonliftability.CoefficientRing.DiscreteValuation
public import FalseTateNonliftability.CoefficientRing.FiniteObstruction
public import FalseTateNonliftability.CoefficientRing.Graded
public import FalseTateNonliftability.CoefficientRing.LocalRing
public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative
public import FalseTateNonliftability.CoefficientRing.Quotient
public import FalseTateNonliftability.CoefficientRing.Substitution
public import FalseTateNonliftability.CoefficientRing.TopLevelObstruction
public import FalseTateNonliftability.CoefficientRing.Truncation
public import FalseTateNonliftability.CoefficientRing.ValuationBound
public import FalseTateNonliftability.Liftability.CoordinateChange
public import FalseTateNonliftability.Liftability.CoordinateFamily
public import FalseTateNonliftability.Liftability.Defs
public import FalseTateNonliftability.Liftability.FieldOfNorms
public import FalseTateNonliftability.Liftability.IsLiftable
public import FalseTateNonliftability.FalseTate.Main
public import FalseTateNonliftability.FalseTate.RamificationNumbers
public import FalseTateNonliftability.FalseTate.TameGenerator

/-!
# Non-liftability of the field of norms of the `p`-adic false Tate curve extension

This library formalizes Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate
curve extension*. Let `p ≥ 3` be a prime and `ℚ_p^FT = ℚ_p(p^{1/p^∞}, ζ_{p^∞})` the false Tate
curve extension. For every finite totally ramified extension `F/ℚ_p`, the action of
`Gal(ℚ_p^FT/ℚ_p)` on the field of norms `X_{ℚ_p}(ℚ_p^FT)` is not `F`-liftable in the sense of
Berger, and the obstruction already occurs modulo `𝔪_F ^ (e + 1)`, where `e = v_F(p)`.

## Main definitions

* Yuan, Definition 1.1 (Berger 2014): `FalseTateNonliftability.IsLiftable p K L F`, the action of
  `Gal(L/K)` on `X_K(L)` is `F`-liftable (`Liftability/IsLiftable`). It is the existence of a lift
  (`FalseTateNonliftability.CoordinateFamily.Lift`,
  `FalseTateNonliftability.CoordinateFamily.Liftable`, `Liftability/Defs`) of the coordinate family
  `FalseTateNonliftability.IsLiftable.coordinateFamily` of the action in a uniformizer. Finite
  lifts modulo `𝔪_F ^ (r + 1)` on a subset of the group are
  `FalseTateNonliftability.CoordinateFamily.FiniteLift` and
  `FalseTateNonliftability.CoordinateFamily.FiniteLiftable`.

## Main results

* Yuan, Proposition 1.3: `FalseTateNonliftability.not_finiteLiftable_falseTate` (for
  `ℚ_p^FT`) and `FalseTateNonliftability.not_finiteLiftable_falseTateExtension` (for
  `ℚ_p(π^{1/p^∞}, ζ_{p^∞})` and any uniformizer `π` of `ℚ_p`), in `FalseTate/Main`. The abstract
  form over a discrete valuation ring is `FalseTateNonliftability.Truncation.false_of_commute`
  (`CoefficientRing/FiniteObstruction`).
* Yuan, Proposition 2.3: `FalseTateNonliftability.isLiftable_iff_uniformizer`,
  `FalseTateNonliftability.isLiftable_iff_exists_uniformizer`,
  `FalseTateNonliftability.isLiftable_iff_forall_uniformizer`,
  `FalseTateNonliftability.IsLiftable.liftable_coordinateFamily_iff` and
  `FalseTateNonliftability.IsLiftable.finiteLiftable_coordinateFamily_iff`
  (`Liftability/IsLiftable`). For an abstract coordinate family and a change of variable these are
  `FalseTateNonliftability.CoordinateFamily.liftable_conj_iff` and
  `FalseTateNonliftability.CoordinateFamily.finiteLiftable_conj_iff`
  (`Liftability/CoordinateChange`).
* Yuan, Theorem A: `FalseTateNonliftability.not_isLiftable_falseTate` (for `ℚ_p^FT`) and
  `FalseTateNonliftability.not_isLiftable_falseTateExtension` (for any uniformizer `π` of `ℚ_p`),
  in `FalseTate/Main`.
* Over `F = ℚ_p`, the Kummer generator alone has no lift modulo `p ^ 2` commuting with a lift of
  Frobenius: `FalseTateNonliftability.not_finiteLiftable_kummerGenerator_bot` (`FalseTate/Main`).

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38
  (Definition 1.1 in Yuan).
-/
