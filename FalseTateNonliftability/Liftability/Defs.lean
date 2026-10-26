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

Let `O` be a local principal ideal ring with maximal ideal `𝔪` and residue field `κ` with `q`
elements; in Yuan, `O` is the ring of integers `𝒪_F` of a finite extension `F` of `ℚ_p`. Let `A`
be the `𝔪`-adic completion of `O((T))` (for `O = 𝒪_F` and a uniformizer `ϖ_F`, the
`ϖ_F`-adic completion of `𝒪_F⟦T⟧[1/T]`), whose reduction modulo `𝔪` is `κ((T))`, and write
`Q ∘ G` for the substitution of `G` for the variable in `Q`. A lift of a coordinate family
`f = (f_g)_{g ∈ Γ}` over `κ` to `A` consists of elements `P` and `F_g`, `g ∈ Γ`, of `A` with
reductions $\bar{P} = T^q$ and $\bar{F}_g = f_g$ such that `F_g ∘ P = P ∘ F_g` and
`F_h ∘ F_g = F_{gh}` for all `g, h ∈ Γ`. When `f` is the coordinate family of the action of
`Gal(L/K)` on the field of norms `X_K(L)` in a uniformizer, the existence of a lift is Berger's
`F`-liftability
(Yuan, Definition 1.1).

A finite lift of `f` modulo `𝔪 ^ (r + 1)` on a subset `S ⊆ Γ` consists of elements `P` and `F_g`,
`g ∈ S`, of `(O ⧸ 𝔪 ^ (r + 1))((T)) = A ⧸ 𝔪 ^ (r + 1) A` with the same reductions such that
`F_g ∘ P = P ∘ F_g` for `g ∈ S`; there is no composition law. Yuan, Proposition 1.4 excludes such
data for the false Tate curve extension, `S = {τ, δ}` and `r = v_F(p)`. The reduction of a lift
modulo `𝔪 ^ (r + 1)` is a finite lift on every subset.

A truncated lift additionally retains the composition law on all of `Γ`. This is the
finite-precision liftability whose coordinate independence is also asserted in Proposition 2.3.

## Main definitions

* `FalseTateNonliftability.CoordinateFamily.Lift f`: lifts of `f` to `A`.
* `FalseTateNonliftability.CoordinateFamily.Liftable f`: `f` has a lift to `A`.
* `FalseTateNonliftability.CoordinateFamily.FiniteLift f S r`: finite lifts of `f` modulo
  `𝔪 ^ (r + 1)` on `S`.
* `FalseTateNonliftability.CoordinateFamily.FiniteLiftable f S r`: `f` has a finite lift modulo
  `𝔪 ^ (r + 1)` on `S`.
* `FalseTateNonliftability.CoordinateFamily.TruncatedLift f r`,
  `FalseTateNonliftability.CoordinateFamily.TruncatedLiftable f r`: lifts modulo `𝔪 ^ (r + 1)`
  satisfying the composition law, and their existence.

## Main results

* `FalseTateNonliftability.CoordinateFamily.Liftable.finiteLiftable`: a coordinate family with a
  lift to `A` has finite lifts modulo every `𝔪 ^ (r + 1)` on every subset.
* `FalseTateNonliftability.CoordinateFamily.Liftable.truncatedLiftable`: reduction of a lift
  to `A` also preserves the composition law.

## Implementation notes

* Truncations are indexed by `r + 1`: `FiniteLift f S r` lives over `O ⧸ 𝔪 ^ (r + 1)`, which has
  residue field `κ` for every `r : ℕ`. The ring `A ⧸ ϖ_F ^ (e + 1) A` of Yuan, §1.5 is `r = e`.
* `TruncatedLift f r` extends `FiniteLift f Set.univ r` by the composition law; the Frobenius,
  lifts and commutation proofs are shared by the two notions.
* `Q ∘ G` is `CoefficientRing.subst G Q` in `A` and `LaurentSeries.subst G Q` in
  `(O ⧸ 𝔪 ^ (r + 1))((T))`. Both are defined for every `G` and are substitution when `G` is
  admissible, that is, when the reduction of `G` modulo `𝔪` has finite positive `T`-adic
  valuation. The `F_g` and, for finite `κ`, `P` are admissible.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Definition 1.1, Proposition 1.4 and Proposition 2.3.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoordinateFamily

open LaurentSeries
open IsLocalRing (ResidueField)

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsPrincipalIdealRing O]
  {Γ : Type*} [Monoid Γ]

/-- A lift of a coordinate family `f = (f_g)_{g ∈ Γ}` over the residue field `κ` of `O` to the
`𝔪`-adic completion `A` of `O((T))` (Yuan, Definition 1.1): elements `P` and `F_g`, `g ∈ Γ`, of `A`
whose reductions in `κ((T))` are $\bar{P} = T^q$, where `q` is the cardinality of `κ`, and
$\bar{F}_g = f_g$, such that `F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}` for all `g, h ∈ Γ`. -/
structure Lift (f : CoordinateFamily (ResidueField O) Γ) where
  /-- The lift `P` of the Frobenius `T^q`. -/
  frobenius : CoefficientRing O
  /-- The lifts `F_g` of the series `f_g`. -/
  lift : Γ → CoefficientRing O
  /-- $\bar{P} = T^q$. -/
  residue_frobenius :
    CoefficientRing.residue O frobenius = HahnSeries.single (Nat.card (ResidueField O) : ℤ) 1
  /-- $\bar{F}_g = f_g$. -/
  residue_lift (g : Γ) :
    CoefficientRing.residue O (lift g) = HahnSeries.ofPowerSeries ℤ _ (f.series g)
  /-- `F_g ∘ P = P ∘ F_g`. -/
  commute (g : Γ) :
    CoefficientRing.subst frobenius (lift g) = CoefficientRing.subst (lift g) frobenius
  /-- `F_h ∘ F_g = F_{gh}`. -/
  lift_mul (g h : Γ) : CoefficientRing.subst (lift g) (lift h) = lift (g * h)

/-- The coordinate family `f` has a lift to the `𝔪`-adic completion `A` of `O((T))`. For the
coordinate family of the action of `Gal(L/K)` on the field of norms `X_K(L)` in a uniformizer, this
is `F`-liftability (Yuan, Definition 1.1). -/
def Liftable (f : CoordinateFamily (ResidueField O) Γ) : Prop :=
  Nonempty f.Lift

/-- A finite lift of a coordinate family `f = (f_g)_{g ∈ Γ}` over the residue field `κ` of `O`
modulo `𝔪 ^ (r + 1)` on a subset `S ⊆ Γ`: elements `P` and `F_g`, `g ∈ S`, of
`(O ⧸ 𝔪 ^ (r + 1))((T))` whose reductions in `κ((T))` are $\bar{P} = T^q$, where `q` is the
cardinality of `κ`, and $\bar{F}_g = f_g$, such that `F_g ∘ P = P ∘ F_g` for `g ∈ S` (Yuan,
Proposition 1.4). -/
structure FiniteLift (f : CoordinateFamily (ResidueField O) Γ) (S : Set Γ) (r : ℕ) where
  /-- The lift `P` of the Frobenius `T^q`. -/
  frobenius : LaurentSeries (Truncation O r)
  /-- The lifts `F_g` of the series `f_g`, `g ∈ S`. -/
  lift : S → LaurentSeries (Truncation O r)
  /-- $\bar{P} = T^q$. -/
  residue_frobenius : mapRingHom (Truncation.residue O r) frobenius =
    HahnSeries.single (Nat.card (ResidueField O) : ℤ) 1
  /-- $\bar{F}_g = f_g$. -/
  residue_lift (g : S) :
    mapRingHom (Truncation.residue O r) (lift g) = HahnSeries.ofPowerSeries ℤ _ (f.series g)
  /-- `F_g ∘ P = P ∘ F_g`. -/
  commute (g : S) : LaurentSeries.subst frobenius (lift g) = LaurentSeries.subst (lift g) frobenius

/-- The coordinate family `f` has a finite lift modulo `𝔪 ^ (r + 1)` on `S`. -/
def FiniteLiftable (f : CoordinateFamily (ResidueField O) Γ) (S : Set Γ) (r : ℕ) : Prop :=
  Nonempty (f.FiniteLift S r)

/-- A lift of the entire coordinate family modulo `𝔪 ^ (r + 1)`, including the composition law
`F_h ∘ F_g = F_{gh}`. This is the finite-precision analogue of `Lift` in Yuan, Proposition 2.3. -/
structure TruncatedLift (f : CoordinateFamily (ResidueField O) Γ) (r : ℕ)
    extends f.FiniteLift Set.univ r where
  /-- `F_h ∘ F_g = F_{gh}` modulo `𝔪 ^ (r + 1)`. -/
  lift_mul (g h : Γ) :
    LaurentSeries.subst (lift ⟨g, Set.mem_univ g⟩) (lift ⟨h, Set.mem_univ h⟩) =
      lift ⟨g * h, Set.mem_univ (g * h)⟩

/-- The coordinate family has a lift modulo `𝔪 ^ (r + 1)` satisfying the composition law. -/
def TruncatedLiftable (f : CoordinateFamily (ResidueField O) Γ) (r : ℕ) : Prop :=
  Nonempty (f.TruncatedLift r)

variable {f : CoordinateFamily (ResidueField O) Γ}

namespace Lift

variable (L : f.Lift)

/-- Each `F_g` is admissible: its reduction `f_g` has `T`-adic valuation `1`. -/
theorem isAdmissible_lift (g : Γ) : CoefficientRing.IsAdmissible (L.lift g) := by
  rw [CoefficientRing.isAdmissible_iff_isAdmissible_residue, L.residue_lift]
  exact isAdmissible_ofPowerSeries (f.constantCoeff_series g) (f.isUnit_coeff_one_series g)

/-- For finite `κ`, the Frobenius lift `P` is admissible: its reduction `T^q` has `T`-adic
valuation `q > 0`. -/
theorem isAdmissible_frobenius [Finite (ResidueField O)] :
    CoefficientRing.IsAdmissible L.frobenius := by
  rw [CoefficientRing.isAdmissible_iff_isAdmissible_residue, L.residue_frobenius]
  exact isAdmissible_single (Nat.cast_pos.mpr Nat.card_pos) isUnit_one

/-- Reducing a lift to `A` modulo `𝔪 ^ (r + 1)` preserves both commutation with Frobenius and
the composition law. -/
def truncate (r : ℕ) : f.TruncatedLift r where
  frobenius := CoefficientRing.reduction O r L.frobenius
  lift g := CoefficientRing.reduction O r (L.lift g)
  residue_frobenius := by
    rw [CoefficientRing.mapRingHom_residue_reduction, L.residue_frobenius]
  residue_lift g := by rw [CoefficientRing.mapRingHom_residue_reduction, L.residue_lift]
  commute g := by
    rw [← CoefficientRing.reduction_subst, ← CoefficientRing.reduction_subst, L.commute]
  lift_mul g h := by rw [← CoefficientRing.reduction_subst, L.lift_mul]

end Lift

namespace FiniteLift

variable {S : Set Γ} {r : ℕ} (L : f.FiniteLift S r)

/-- Each `F_g`, `g ∈ S`, is admissible: its reduction `f_g` has `T`-adic valuation `1`. -/
theorem isAdmissible_lift (g : S) : IsAdmissible (L.lift g) := by
  rw [← isAdmissible_mapRingHom_iff (Truncation.residue O r), L.residue_lift]
  exact isAdmissible_ofPowerSeries (f.constantCoeff_series g) (f.isUnit_coeff_one_series g)

/-- For finite `κ`, the Frobenius lift `P` is admissible: its reduction `T^q` has `T`-adic
valuation `q > 0`. -/
theorem isAdmissible_frobenius [Finite (ResidueField O)] : IsAdmissible L.frobenius := by
  rw [← isAdmissible_mapRingHom_iff (Truncation.residue O r), L.residue_frobenius]
  exact isAdmissible_single (Nat.cast_pos.mpr Nat.card_pos) isUnit_one

end FiniteLift

/-- A lift modulo `𝔪 ^ (r + 1)` satisfying the composition law gives commuting lifts on every
prescribed subset of `Γ`. -/
theorem TruncatedLiftable.finiteLiftable {r : ℕ} (hf : f.TruncatedLiftable r) (S : Set Γ) :
    f.FiniteLiftable S r := by
  obtain ⟨L⟩ := hf
  exact ⟨{
    frobenius := L.frobenius
    lift g := L.lift ⟨g, Set.mem_univ g⟩
    residue_frobenius := L.residue_frobenius
    residue_lift g := L.residue_lift ⟨g, Set.mem_univ g⟩
    commute g := L.commute ⟨g, Set.mem_univ g⟩ }⟩

/-- A lift to `A` gives a lift modulo every `𝔪 ^ (r + 1)` satisfying the composition law. -/
theorem Liftable.truncatedLiftable (hf : f.Liftable) (r : ℕ) : f.TruncatedLiftable r :=
  hf.map fun L ↦ L.truncate r

/-- A coordinate family with a lift to `A` has a finite lift modulo every `𝔪 ^ (r + 1)` on every
subset of `Γ`, namely the reduction of the lift modulo `𝔪 ^ (r + 1)`. -/
theorem Liftable.finiteLiftable (hf : f.Liftable) (S : Set Γ) (r : ℕ) : f.FiniteLiftable S r :=
  (hf.truncatedLiftable r).finiteLiftable S

end FalseTateNonliftability.CoordinateFamily
