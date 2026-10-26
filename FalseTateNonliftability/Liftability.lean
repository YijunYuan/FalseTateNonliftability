/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Liftability.CoordinateChange
public import FalseTateNonliftability.Liftability.CoordinateFamily
public import FalseTateNonliftability.Liftability.Defs
public import FalseTateNonliftability.Liftability.FieldOfNorms
public import FalseTateNonliftability.Liftability.IsLiftable
public import FalseTateNonliftability.Liftability.TotallyRamified

/-!
# Liftability

Lifts of coordinate families and Berger's `F`-liftability of the action of `Gal(L/K)` on the field
of norms `X_K(L)`. A coordinate family over a field `κ` is a family of power series
`f_g ∈ T κ⟦T⟧`, `g ∈ Γ`, with `f_g'(0) ≠ 0` and `f_{gh} = f_h ∘ f_g`, such as the series of the
images of a uniformizer `u` of `X_K(L)` under `Gal(L/K)` (Yuan, Lemma 2.2). A lift to the
`𝔪_F`-adic completion `A_K` of `𝒪_F((T))` consists of a lift `P` of `T^q` and lifts `F_g` of the
`f_g` with `F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}` (Yuan, Definition 1.1); finite lifts
modulo `𝔪_F ^ (r + 1)` on a subset of `Γ` are the data excluded by Yuan, Proposition 1.4. A
change of uniformizer conjugates the coordinate family, which does not change liftability
(Yuan, Proposition 2.3).

## Main definitions

* `FontaineWintenberger.IsTotallyRamified`, `IntermediateField.HasSameResidueField`
  (`Liftability/TotallyRamified`): total ramification and equality of residue fields.
* `FalseTateNonliftability.CoordinateFamily` (`Liftability/CoordinateFamily`).
* `FalseTateNonliftability.CoordinateFamily.Lift`,
  `FalseTateNonliftability.CoordinateFamily.Liftable`,
  `FalseTateNonliftability.CoordinateFamily.FiniteLift`,
  `FalseTateNonliftability.CoordinateFamily.FiniteLiftable`,
  `FalseTateNonliftability.CoordinateFamily.TruncatedLift`,
  `FalseTateNonliftability.CoordinateFamily.TruncatedLiftable` (`Liftability/Defs`).
* `FalseTateNonliftability.FieldOfNorms.coordinateFamily`: the coordinate family of `X_K(L)` in a
  uniformizer (`Liftability/FieldOfNorms`, Yuan, Lemma 2.2).
* `FalseTateNonliftability.IsLiftable`: `F`-liftability (`Liftability/IsLiftable`, Yuan,
  Definition 1.1).

## Main results

* `FalseTateNonliftability.CoordinateFamily.liftable_conj_iff`,
  `FalseTateNonliftability.CoordinateFamily.truncatedLiftable_conj_iff`,
  `FalseTateNonliftability.CoordinateFamily.finiteLiftable_conj_iff`
  (`Liftability/CoordinateChange`) and `FalseTateNonliftability.isLiftable_iff_uniformizer`
  (`Liftability/IsLiftable`): Yuan, Proposition 2.3.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Definition 1.1, Lemma 2.2, Proposition 1.4 and Proposition 2.3.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/
