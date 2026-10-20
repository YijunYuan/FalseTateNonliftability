/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Substitution
public import FalseTateNonliftability.Liftability.Defs
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Independence of the uniformizer

Let `O` be a local principal ideal ring with maximal ideal `𝔪` and finite residue field `κ` with
`q` elements, let `A` be the `𝔪`-adic completion of `O((T))`, let `f = (f_g)_{g ∈ Γ}` be a
coordinate family over `κ`, and let `w ∈ κ⟦T⟧` with `w(0) = 0` and `w'(0) ≠ 0`. Then the
coordinate family `(w ∘ f_g ∘ w^{∘-1})_{g ∈ Γ}` has a lift to `A` if and only if `f` has one, and
the same holds for finite lifts modulo every `𝔪 ^ (r + 1)` on every subset of `Γ`. Indeed, let
`H` be a power series over `O` (or over `O ⧸ 𝔪 ^ (r + 1)`) with `H(0) = 0` reducing to `w`; its
compositional inverse reduces to `w^{∘-1}` (Yuan, Lemma 2.1 (3)). Conjugation `Q ↦ H ∘ Q ∘ H^{∘-1}`
preserves the relations `F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}`, maps `F_g` to a lift of
`w ∘ f_g ∘ w^{∘-1}`, and maps `P` to a lift of `T^q`, since `T^q ∘ w = w^q = w ∘ T^q` over the
field with `q` elements.

By Yuan, Lemma 2.2 (4), replacing the uniformizer `u` of the field of norms by `ev_u(w)` replaces
its coordinate family `f` by `w ∘ f ∘ w^{∘-1}`, so `F`-liftability does not depend on the
uniformizer (Yuan, Proposition 2.3).

## Main results

* `LaurentSeries.conj_single_natCard`: over a field with `q` elements, conjugation by a power
  series fixes `T^q`.
* `FalseTateNonliftability.CoordinateFamily.liftable_conj_iff`: `w ∘ f ∘ w^{∘-1}` has a lift to
  `A` if and only if `f` has one (Yuan, Proposition 2.3).
* `FalseTateNonliftability.CoordinateFamily.finiteLiftable_conj_iff`: `w ∘ f ∘ w^{∘-1}` has a
  finite lift modulo `𝔪 ^ (r + 1)` on `S` if and only if `f` has one (Yuan, Proposition 2.3).

## Implementation notes

The two equivalences are stated for every power series `w`: `f.conj w = f` unless `w(0) = 0` and
`w'(0)` is a unit.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.1, Lemma 2.2 and Proposition 2.3.
-/

public section

noncomputable section

namespace LaurentSeries

variable {k : Type*} [Field k] [Finite k]

/-- Over a field with `q` elements, conjugation by a power series `w` with `w(0) = 0` and
`w'(0) ≠ 0` fixes the Frobenius: `w ∘ T^q ∘ w^{∘-1} = T^q`. -/
theorem conj_single_natCard {w : PowerSeries k} (hw : w.constantCoeff = 0)
    (hw' : IsUnit (w.coeff 1)) :
    conj w (HahnSeries.single (Nat.card k : ℤ) 1) = HahnSeries.single (Nat.card k : ℤ) 1 := by
  have hq : HahnSeries.single (Nat.card k : ℤ) (1 : k) = HahnSeries.single 1 1 ^ Nat.card k := by
    rw [HahnSeries.single_pow, one_pow, nsmul_one]
  rw [conj_eq_iff_subst hw hw', subst_single_natCard_eq_pow, hq, map_pow,
    subst_X (isAdmissible_ofPowerSeries hw hw')]

end LaurentSeries

namespace FalseTateNonliftability.CoordinateFamily

open LaurentSeries
open IsLocalRing (ResidueField)

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsPrincipalIdealRing O]
  [Finite (ResidueField O)] {Γ : Type*} [Monoid Γ] {f : CoordinateFamily (ResidueField O) Γ}

/-- If `f` has a lift to `A`, so has the coordinate family `w ∘ f ∘ w^{∘-1}` obtained by the change
of variable `T' = w(T)`. -/
theorem Liftable.conj (hf : f.Liftable) (w : PowerSeries (ResidueField O)) :
    (f.conj w).Liftable := by
  by_cases hw : w.constantCoeff = 0 ∧ IsUnit (w.coeff 1)
  swap
  · rwa [conj_of_not f hw]
  obtain ⟨H, hH, hl, rfl⟩ := CoefficientRing.exists_map_residue_eq w hw.1 hw.2
  obtain ⟨L⟩ := hf
  exact ⟨{
    frobenius := CoefficientRing.conj H L.frobenius
    lift g := CoefficientRing.conj H (L.lift g)
    residue_frobenius := by
      rw [CoefficientRing.residue_conj hH hl, L.residue_frobenius,
        LaurentSeries.conj_single_natCard hw.1 hw.2]
    residue_lift g := by
      rw [conj_series f hw.1 hw.2, CoefficientRing.residue_conj_of_residue_eq hH hl
        (L.isAdmissible_lift g) (f.constantCoeff_series g) (L.residue_lift g)]
    commute g := (CoefficientRing.conj_commute_iff hH hl L.isAdmissible_frobenius
      (L.isAdmissible_lift g)).mpr (L.commute g)
    lift_mul g h := by
      rw [← CoefficientRing.conj_subst hH hl (L.isAdmissible_lift g) (L.isAdmissible_lift h),
        L.lift_mul] }⟩

/-- Yuan, Proposition 2.3: the coordinate family `w ∘ f ∘ w^{∘-1}` obtained by the change of
variable `T' = w(T)` has a lift to `A` if and only if `f` has one. -/
theorem liftable_conj_iff (w : PowerSeries (ResidueField O)) :
    (f.conj w).Liftable ↔ f.Liftable := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj w⟩
  by_cases hw : w.constantCoeff = 0 ∧ IsUnit (w.coeff 1)
  · simpa only [conj_compInv_conj f hw.1 hw.2] using h.conj w.compInv
  · rwa [conj_of_not f hw] at h

variable {S : Set Γ} {r : ℕ}

/-- If `f` has a finite lift modulo `𝔪 ^ (r + 1)` on `S`, so has the coordinate family
`w ∘ f ∘ w^{∘-1}` obtained by the change of variable `T' = w(T)`. -/
theorem FiniteLiftable.conj (hf : f.FiniteLiftable S r) (w : PowerSeries (ResidueField O)) :
    (f.conj w).FiniteLiftable S r := by
  by_cases hw : w.constantCoeff = 0 ∧ IsUnit (w.coeff 1)
  swap
  · rwa [conj_of_not f hw]
  obtain ⟨H, hH, hl, rfl⟩ := Truncation.exists_map_residue_eq r w hw.1 hw.2
  obtain ⟨L⟩ := hf
  exact ⟨{
    frobenius := LaurentSeries.conj H L.frobenius
    lift g := LaurentSeries.conj H (L.lift g)
    residue_frobenius := by
      rw [mapRingHom_conj _ hH hl, L.residue_frobenius,
        LaurentSeries.conj_single_natCard hw.1 hw.2]
    residue_lift g := by
      rw [conj_series f hw.1 hw.2, mapRingHom_conj_of_mapRingHom_eq _ hH hl
        (L.isAdmissible_lift g) (f.constantCoeff_series g) (L.residue_lift g)]
    commute g := (LaurentSeries.conj_commute_iff hH hl L.isAdmissible_frobenius
      (L.isAdmissible_lift g)).mpr (L.commute g) }⟩

/-- Yuan, Proposition 2.3 modulo `𝔪 ^ (r + 1)`: the coordinate family `w ∘ f ∘ w^{∘-1}` obtained
by the change of variable `T' = w(T)` has a finite lift modulo `𝔪 ^ (r + 1)` on `S` if and only
if `f` has one. -/
theorem finiteLiftable_conj_iff (w : PowerSeries (ResidueField O)) :
    (f.conj w).FiniteLiftable S r ↔ f.FiniteLiftable S r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.conj w⟩
  by_cases hw : w.constantCoeff = 0 ∧ IsUnit (w.coeff 1)
  · simpa only [conj_compInv_conj f hw.1 hw.2] using h.conj w.compInv
  · rwa [conj_of_not f hw] at h

end FalseTateNonliftability.CoordinateFamily
