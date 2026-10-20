/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Substitution
public import FalseTateNonliftability.Liftability.CoordinateFamily

/-!
# Lifts of coordinate families

Let `O` be a discrete valuation ring with maximal ideal `𝔪` and finite residue field `κ` with `q`
elements, for instance the ring of integers of a finite extension `F` of `ℚ_p`, and let `A` be the
`𝔪`-adic completion of `O((T))` (`FalseTateNonliftability.CoefficientRing O`), whose reduction
modulo `𝔪` is `κ((T))`. Write `Q ∘ G` for the substitution of `G` for the variable in `Q`. A lift
of a coordinate family `f = (f_g)_{g ∈ Γ}` over `κ` to `A` consists of elements `P` and `F_g`,
`g ∈ Γ`, of `A` with reductions `P̄ = T^q` and `F̄_g = f_g` such that `F_g ∘ P = P ∘ F_g` and
`F_h ∘ F_g = F_{gh}` for all `g, h ∈ Γ`. When `f` is the coordinate family of the action of
`Gal(L/K)` on the field of norms `X_K(L)` in a uniformizer, the existence of a lift is Berger's
`F`-liftability (Yuan, Definition 1.1).

A finite lift of `f` modulo `𝔪 ^ (r + 1)` on a subset `S ⊆ Γ` consists of elements `P` and `F_g`,
`g ∈ S`, of `(O ⧸ 𝔪 ^ (r + 1))((T)) = A ⧸ 𝔪 ^ (r + 1) A` with the same reductions such that
`F_g ∘ P = P ∘ F_g` for `g ∈ S`; there is no composition law. Yuan, Proposition 1.3 excludes such
data for the false Tate curve extension, `S = {τ, δ}` and `r = v_F(p)`. The reduction of a lift
modulo `𝔪 ^ (r + 1)` is a finite lift on every subset.

## Main definitions

* `FalseTateNonliftability.CoordinateFamily.Lift f`: lifts of `f` to `A`.
* `FalseTateNonliftability.CoordinateFamily.Liftable f`: `f` has a lift to `A`.
* `FalseTateNonliftability.CoordinateFamily.FiniteLift f S r`: finite lifts of `f` modulo
  `𝔪 ^ (r + 1)` on `S`.
* `FalseTateNonliftability.CoordinateFamily.FiniteLiftable f S r`: `f` has a finite lift modulo
  `𝔪 ^ (r + 1)` on `S`.

## Main results

* `FalseTateNonliftability.CoordinateFamily.Liftable.finiteLiftable`: a coordinate family with a
  lift to `A` has finite lifts modulo every `𝔪 ^ (r + 1)` on every subset.

## References

* Yuan, Definition 1.1 and Proposition 1.3.
* Berger 2014, Definition 1.1 in Yuan.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoordinateFamily

open LaurentSeries
open IsLocalRing (ResidueField)

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsPrincipalIdealRing O]
  {Γ : Type*} [Monoid Γ]

/-- A lift of a coordinate family `f = (f_g)_{g ∈ Γ}` over the residue field `κ` of `O` to the
coefficient ring `A` (Yuan, Definition 1.1): elements `P` and `F_g`, `g ∈ Γ`, of `A` whose images
in `κ((T))` are `T^q`, where `q` is the cardinality of `κ`, and `f_g`, such that
`F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}`. Here `Q ∘ G` is `CoefficientRing.subst G Q`. -/
structure Lift (f : CoordinateFamily (ResidueField O) Γ) where
  /-- The lift `P` of the Frobenius `T^q`. -/
  frobenius : CoefficientRing O
  /-- The lifts `F_g` of the series `f_g`. -/
  lift : Γ → CoefficientRing O
  /-- `P̄ = T^q`. -/
  residue_frobenius :
    CoefficientRing.residue O frobenius = HahnSeries.single (Nat.card (ResidueField O) : ℤ) 1
  /-- `F̄_g = f_g`. -/
  residue_lift (g : Γ) :
    CoefficientRing.residue O (lift g) = HahnSeries.ofPowerSeries ℤ _ (f.series g)
  /-- `F_g ∘ P = P ∘ F_g`. -/
  commute (g : Γ) :
    CoefficientRing.subst frobenius (lift g) = CoefficientRing.subst (lift g) frobenius
  /-- `F_h ∘ F_g = F_{gh}`. -/
  lift_mul (g h : Γ) : CoefficientRing.subst (lift g) (lift h) = lift (g * h)

/-- The coordinate family `f` has a lift to `A`. For the coordinate family of the action of
`Gal(L/K)` on the field of norms `X_K(L)` in a uniformizer, this is `F`-liftability
(Yuan, Definition 1.1). -/
def Liftable (f : CoordinateFamily (ResidueField O) Γ) : Prop :=
  Nonempty f.Lift

/-- A finite lift of a coordinate family `f = (f_g)_{g ∈ Γ}` over the residue field `κ` of `O`
modulo `𝔪 ^ (r + 1)` on a subset `S ⊆ Γ`: elements `P` and `F_g`, `g ∈ S`, of
`(O ⧸ 𝔪 ^ (r + 1))((T))` whose images in `κ((T))` are `T^q`, where `q` is the cardinality of `κ`,
and `f_g`, such that `F_g ∘ P = P ∘ F_g` (the data of Yuan, Proposition 1.3). -/
structure FiniteLift (f : CoordinateFamily (ResidueField O) Γ) (S : Set Γ) (r : ℕ) where
  /-- The lift `P` of the Frobenius `T^q`. -/
  frobenius : LaurentSeries (Truncation O r)
  /-- The lifts `F_g` of the series `f_g`, `g ∈ S`. -/
  lift : S → LaurentSeries (Truncation O r)
  /-- `P̄ = T^q`. -/
  residue_frobenius : mapRingHom (Truncation.residue O r) frobenius =
    HahnSeries.single (Nat.card (ResidueField O) : ℤ) 1
  /-- `F̄_g = f_g`. -/
  residue_lift (g : S) :
    mapRingHom (Truncation.residue O r) (lift g) = HahnSeries.ofPowerSeries ℤ _ (f.series g)
  /-- `F_g ∘ P = P ∘ F_g`. -/
  commute (g : S) : LaurentSeries.subst frobenius (lift g) = LaurentSeries.subst (lift g) frobenius

/-- The coordinate family `f` has a finite lift modulo `𝔪 ^ (r + 1)` on `S`. -/
def FiniteLiftable (f : CoordinateFamily (ResidueField O) Γ) (S : Set Γ) (r : ℕ) : Prop :=
  Nonempty (f.FiniteLift S r)

variable {f : CoordinateFamily (ResidueField O) Γ}

namespace Lift

variable (L : f.Lift)

/-- The lifts `F_g` are admissible. -/
theorem isAdmissible_lift (g : Γ) : CoefficientRing.IsAdmissible (L.lift g) := by
  rw [CoefficientRing.isAdmissible_iff_isAdmissible_residue, L.residue_lift]
  exact isAdmissible_ofPowerSeries (f.constantCoeff_series g) (f.isUnit_coeff_one_series g)

/-- The Frobenius lift `P` is admissible. -/
theorem isAdmissible_frobenius [Finite (ResidueField O)] :
    CoefficientRing.IsAdmissible L.frobenius := by
  rw [CoefficientRing.isAdmissible_iff_isAdmissible_residue, L.residue_frobenius]
  exact isAdmissible_single (Nat.cast_pos.mpr Nat.card_pos) isUnit_one

end Lift

namespace FiniteLift

variable {S : Set Γ} {r : ℕ} (L : f.FiniteLift S r)

/-- The lifts `F_g`, `g ∈ S`, are admissible. -/
theorem isAdmissible_lift (g : S) : IsAdmissible (L.lift g) := by
  rw [← isAdmissible_mapRingHom_iff (Truncation.residue O r), L.residue_lift]
  exact isAdmissible_ofPowerSeries (f.constantCoeff_series g) (f.isUnit_coeff_one_series g)

/-- The Frobenius lift `P` is admissible. -/
theorem isAdmissible_frobenius [Finite (ResidueField O)] : IsAdmissible L.frobenius := by
  rw [← isAdmissible_mapRingHom_iff (Truncation.residue O r), L.residue_frobenius]
  exact isAdmissible_single (Nat.cast_pos.mpr Nat.card_pos) isUnit_one

end FiniteLift

/-- A coordinate family with a lift to `A` has a finite lift modulo every `𝔪 ^ (r + 1)` on every
subset of `Γ`: the reduction of the lift. -/
theorem Liftable.finiteLiftable (hf : f.Liftable) (S : Set Γ) (r : ℕ) : f.FiniteLiftable S r := by
  obtain ⟨L⟩ := hf
  exact ⟨{
    frobenius := CoefficientRing.reduction O r L.frobenius
    lift g := CoefficientRing.reduction O r (L.lift g)
    residue_frobenius := by
      rw [CoefficientRing.mapRingHom_residue_reduction, L.residue_frobenius]
    residue_lift g := by rw [CoefficientRing.mapRingHom_residue_reduction, L.residue_lift]
    commute g := by
      rw [← CoefficientRing.reduction_subst, ← CoefficientRing.reduction_subst, L.commute] }⟩

end FalseTateNonliftability.CoordinateFamily
