/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Substitution

/-!
# Coordinate changes

Let `R` be a local Artinian ring with principal maximal ideal, and let `H` be a power series over
`R` with `H(0) = 0` and `H'(0)` a unit, with compositional inverse `H^{∘-1}`. The conjugate of a
Laurent series `P` by `H` is `H ∘ P ∘ H^{∘-1}`, where `f ∘ G` denotes substitution of `G` in `f`.
On the coefficient ring `A` the conjugate of `P ∈ A` by a power series `H` over `O` is defined in
the same way, and it reduces modulo every `𝔪 ^ (r + 1)` to the conjugate by the reduction of `H`.

Conjugation by `H` fixes the variable, preserves admissibility, is inverted by conjugation by
`H^{∘-1}`, preserves composition (`H ∘ (P ∘ G) ∘ H^{∘-1}` is the composite of the conjugates of
`P` and `G`) and hence commutation, and it commutes with coefficient maps. On power series over
the residue field it is `PowerSeries.conj`. Every power series `w` over the residue field `κ` of
`O` with `w(0) = 0` and `w'(0) ≠ 0` lifts coefficientwise to a power series `H` over `O` with
`H(0) = 0` and `H'(0)` a unit. These are the ingredients of Yuan, Proposition 2.3: if
`π' = ev_π(w)` is another uniformizer of the field of norms, conjugation by such a lift `H`
transports lifts with respect to `π` to lifts with respect to `π'`, in `A` and modulo every power
of `𝔪`.

## Main definitions

* `LaurentSeries.conj H P`: the conjugate `H ∘ P ∘ H^{∘-1}` of a Laurent series `P`.
* `CoefficientRing.conj H P`: the conjugate `H ∘ P ∘ H^{∘-1}` of `P ∈ A`.

## Main results

* `LaurentSeries.conj_eq_iff_subst`: `H ∘ P ∘ H^{∘-1} = Q` if and only if `H ∘ P = Q ∘ H`.
* `LaurentSeries.conj_subst`, `LaurentSeries.conj_commute_iff`: conjugation preserves
  composition, and preserves and reflects commutation of admissible series.
* `LaurentSeries.mapRingHom_conj`, `LaurentSeries.conj_ofPowerSeries`: conjugation commutes with
  coefficient maps and is `PowerSeries.conj` on power series.
* `CoefficientRing.reduction_conj`, `CoefficientRing.residue_conj`: conjugation in `A` reduces to
  conjugation over `O ⧸ 𝔪 ^ (r + 1)` and over `κ`.
* `CoefficientRing.conj_subst`, `CoefficientRing.conj_commute_iff`: the same laws in `A`.
* `CoefficientRing.exists_map_residue_eq`, `Truncation.exists_map_residue_eq`: coefficientwise
  lifts of coordinate changes over `κ`.

## References

* Yuan, Lemma 2.1 (3) and Proposition 2.3.
-/

public section

noncomputable section

private theorem constantCoeff_map_eq_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {H : PowerSeries R} (hH : H.constantCoeff = 0) : (H.map φ).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hH, map_zero]

private theorem isUnit_coeff_one_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {H : PowerSeries R} (hl : IsUnit (H.coeff 1)) : IsUnit ((H.map φ).coeff 1) := by
  rw [PowerSeries.coeff_map]
  exact hl.map φ

namespace LaurentSeries

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]
  [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsPrincipalIdealRing S]

/-- The conjugate `H ∘ P ∘ H^{∘-1}` of a Laurent series `P` by a power series `H`, where
`H^{∘-1}` is the compositional inverse of `H` (`PowerSeries.compInv`). -/
@[expose] def conj (H : PowerSeries R) (P : LaurentSeries R) : LaurentSeries R :=
  subst (HahnSeries.ofPowerSeries ℤ R H.compInv) (subst P (HahnSeries.ofPowerSeries ℤ R H))

variable {H : PowerSeries R}

omit [IsArtinianRing R] [IsPrincipalIdealRing R] in
private theorem isAdmissible_ofPowerSeries_compInv (H : PowerSeries R) :
    IsAdmissible (HahnSeries.ofPowerSeries ℤ R H.compInv) :=
  isAdmissible_ofPowerSeries (PowerSeries.constantCoeff_compInv H)
    (PowerSeries.isUnit_coeff_one_compInv H)

private theorem subst_ofPowerSeries_compInv (hH : H.constantCoeff = 0)
    (hl : IsUnit (H.coeff 1)) (f : LaurentSeries R) :
    subst (HahnSeries.ofPowerSeries ℤ R H.compInv) f = (substEquiv H).symm f := by
  rw [substEquiv_symm_apply hH hl, PowerSeries.compInv_eq_substInvOfIsUnit hl]

/-- `H ∘ P ∘ H^{∘-1}` is the image of `H ∘ P` under the inverse of `f ↦ f(H)`. -/
theorem conj_eq_substEquiv_symm (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : LaurentSeries R) :
    conj H P = (substEquiv H).symm (subst P (HahnSeries.ofPowerSeries ℤ R H)) :=
  subst_ofPowerSeries_compInv hH hl _

/-- `H ∘ P ∘ H^{∘-1} = Q` if and only if `H ∘ P = Q ∘ H`. -/
theorem conj_eq_iff_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P Q : LaurentSeries R} :
    conj H P = Q ↔
      subst P (HahnSeries.ofPowerSeries ℤ R H) = subst (HahnSeries.ofPowerSeries ℤ R H) Q := by
  rw [conj_eq_substEquiv_symm hH hl, AlgEquiv.symm_apply_eq, substEquiv_apply hH hl]

/-- `(H ∘ P ∘ H^{∘-1}) ∘ H = H ∘ P`. -/
theorem subst_ofPowerSeries_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : LaurentSeries R) :
    subst (HahnSeries.ofPowerSeries ℤ R H) (conj H P) =
      subst P (HahnSeries.ofPowerSeries ℤ R H) :=
  ((conj_eq_iff_subst hH hl).mp rfl).symm

/-- Conjugation fixes the variable. -/
theorem conj_X_right (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    conj H (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single 1 1 := by
  rw [conj_eq_iff_subst hH hl, subst_X_left_apply, subst_X (isAdmissible_ofPowerSeries hH hl)]

/-- Conjugation by the variable is the identity on admissible series. -/
theorem conj_X {P : LaurentSeries R} (hP : IsAdmissible P) : conj PowerSeries.X P = P := by
  rw [conj, PowerSeries.compInv_X, HahnSeries.ofPowerSeries_X, subst_X hP, subst_X_left_apply]

/-- Conjugation preserves admissibility. -/
theorem IsAdmissible.conj {P : LaurentSeries R} (hP : IsAdmissible P)
    (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) : IsAdmissible (LaurentSeries.conj H P) :=
  ((isAdmissible_ofPowerSeries hH hl).subst hP).subst (isAdmissible_ofPowerSeries_compInv H)

/-- Substitution of `H ∘ P ∘ H^{∘-1}` is substitution of `P` conjugated by `f ↦ f(H)`:
`f ∘ (H ∘ P ∘ H^{∘-1}) = ((f ∘ H) ∘ P) ∘ H^{∘-1}`. -/
theorem subst_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (P : LaurentSeries R) :
    subst (conj H P) =
      ((substEquiv H).symm.toAlgHom.comp (subst P)).comp (substEquiv H).toAlgHom := by
  by_cases hP : IsAdmissible P
  · let := orderTopology R
    refine (subst_unique (hP.conj hH hl) _ ((continuous_substEquiv_symm H).comp
      ((continuous_subst P).comp (continuous_substEquiv H))) ?_).symm
    change (substEquiv H).symm (subst P (substEquiv H (HahnSeries.single 1 1))) = _
    rw [substEquiv_X hH hl, conj_eq_substEquiv_symm hH hl]
  · rw [conj_eq_substEquiv_symm hH hl, subst_of_not_isAdmissible hP, AlgHom.id_apply,
      ← substEquiv_X hH hl, AlgEquiv.symm_apply_apply, subst_X_left]
    exact AlgHom.ext fun f ↦ ((substEquiv H).symm_apply_apply f).symm

theorem subst_conj_apply (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P f : LaurentSeries R) :
    subst (conj H P) f = (substEquiv H).symm (subst P (substEquiv H f)) :=
  AlgHom.congr_fun (subst_conj hH hl P) f

/-- Conjugation preserves composition: `H ∘ (P ∘ G) ∘ H^{∘-1}` is the composite of
`H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`. -/
theorem conj_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) {G P : LaurentSeries R}
    (hG : IsAdmissible G) (hP : IsAdmissible P) :
    conj H (subst G P) = subst (conj H G) (conj H P) := by
  rw [subst_conj_apply hH hl, substEquiv_apply hH hl, subst_ofPowerSeries_conj hH hl,
    subst_comp_subst_apply hP hG, conj_eq_substEquiv_symm hH hl]

/-- Conjugating by `H` and then by `H^{∘-1}` is the identity on admissible series. -/
theorem conj_compInv_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : LaurentSeries R} (hP : IsAdmissible P) : conj H.compInv (conj H P) = P := by
  rw [conj_eq_iff_subst (PowerSeries.constantCoeff_compInv H)
      (PowerSeries.isUnit_coeff_one_compInv H), subst_conj_apply hH hl,
    substEquiv_ofPowerSeries hH hl, PowerSeries.subst_compInv_left hH hl,
    HahnSeries.ofPowerSeries_X, subst_X hP, subst_ofPowerSeries_compInv hH hl]

/-- Conjugating by `H^{∘-1}` and then by `H` is the identity on admissible series. -/
theorem conj_conj_compInv (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : LaurentSeries R} (hP : IsAdmissible P) : conj H (conj H.compInv P) = P := by
  have h := conj_compInv_conj (PowerSeries.constantCoeff_compInv H)
    (PowerSeries.isUnit_coeff_one_compInv H) hP
  rwa [PowerSeries.compInv_compInv hH hl] at h

theorem conj_inj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) {P G : LaurentSeries R}
    (hP : IsAdmissible P) (hG : IsAdmissible G) : conj H P = conj H G ↔ P = G :=
  ⟨fun h ↦ by rw [← conj_compInv_conj hH hl hP, h, conj_compInv_conj hH hl hG],
    fun h ↦ h ▸ rfl⟩

/-- Conjugation preserves and reflects commutation: `H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`
commute if and only if `P` and `G` commute. -/
theorem conj_commute_iff (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P G : LaurentSeries R} (hP : IsAdmissible P) (hG : IsAdmissible G) :
    subst (conj H P) (conj H G) = subst (conj H G) (conj H P) ↔ subst P G = subst G P := by
  rw [← conj_subst hH hl hP hG, ← conj_subst hH hl hG hP,
    conj_inj hH hl (hG.subst hP) (hP.subst hG)]

/-- Conjugation commutes with coefficient maps. -/
theorem mapRingHom_conj (φ : R →+* S) (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : LaurentSeries R) : mapRingHom φ (conj H P) = conj (H.map φ) (mapRingHom φ P) := by
  rw [conj, conj, mapRingHom_subst', mapRingHom_subst', mapRingHom_ofPowerSeries,
    mapRingHom_ofPowerSeries, PowerSeries.map_compInv φ hH hl]

/-- On power series `f` with `f(0) = 0`, conjugation is `PowerSeries.conj`. -/
theorem conj_ofPowerSeries {f : PowerSeries R} (hf : f.constantCoeff = 0)
    (hfadm : IsAdmissible (HahnSeries.ofPowerSeries ℤ R f)) (H : PowerSeries R) :
    conj H (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.conj H f) := by
  rw [conj, subst_ofPowerSeries hf hfadm, subst_ofPowerSeries (PowerSeries.constantCoeff_compInv H)
    (isAdmissible_ofPowerSeries_compInv H)]
  rfl

/-- If the image of an admissible `P` under a coefficient map `φ` is a power series `f`, then the
image of `H ∘ P ∘ H^{∘-1}` is `PowerSeries.conj` of `f` by `φ H`. -/
theorem mapRingHom_conj_of_mapRingHom_eq (φ : R →+* S) (hH : H.constantCoeff = 0)
    (hl : IsUnit (H.coeff 1)) {P : LaurentSeries R} (hP : IsAdmissible P) {f : PowerSeries S}
    (hf : f.constantCoeff = 0) (hres : mapRingHom φ P = HahnSeries.ofPowerSeries ℤ S f) :
    mapRingHom φ (conj H P) = HahnSeries.ofPowerSeries ℤ S (PowerSeries.conj (H.map φ) f) := by
  rw [mapRingHom_conj φ hH hl, hres, conj_ofPowerSeries hf (hres ▸ hP.map φ)]

end LaurentSeries

namespace FalseTateNonliftability

open LaurentSeries
open IsLocalRing (ResidueField)

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- A power series `w` over the residue field of `O` with `w(0) = 0` and `w'(0) ≠ 0` is the
coefficientwise reduction of a power series `H` over `O` with `H(0) = 0` and `H'(0)` a unit. -/
theorem CoefficientRing.exists_map_residue_eq (w : PowerSeries (ResidueField O))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    ∃ H : PowerSeries O, H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) ∧
      H.map (IsLocalRing.residue O) = w := by
  obtain ⟨H, hH⟩ := PowerSeries.map_surjective _ IsLocalRing.residue_surjective w
  have hc : IsLocalRing.residue O H.constantCoeff = 0 := by
    rw [← hw, ← hH, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  have hl : IsUnit (H.coeff 1) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← PowerSeries.coeff_map, hH]
    exact hw'.ne_zero
  refine ⟨H - PowerSeries.C H.constantCoeff, by simp, by simpa using hl, ?_⟩
  rw [map_sub, PowerSeries.map_C, hc, map_zero, sub_zero, hH]

/-- A power series `w` over the residue field of `O` with `w(0) = 0` and `w'(0) ≠ 0` is the
coefficientwise reduction of a power series `H` over `O ⧸ 𝔪 ^ (r + 1)` with `H(0) = 0` and
`H'(0)` a unit. -/
theorem Truncation.exists_map_residue_eq (r : ℕ) (w : PowerSeries (ResidueField O))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    ∃ H : PowerSeries (Truncation O r), H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) ∧
      H.map (Truncation.residue O r) = w := by
  obtain ⟨H, hH, hl, hres⟩ := CoefficientRing.exists_map_residue_eq w hw hw'
  refine ⟨H.map (Truncation.mk O r), constantCoeff_map_eq_zero _ hH, isUnit_coeff_one_map _ hl,
    ?_⟩
  change PowerSeries.map ((Truncation.residue O r).comp (Truncation.mk O r)) H = w
  rw [Truncation.residue_comp_mk, hres]

namespace CoefficientRing

variable [IsPrincipalIdealRing O]

/-- The conjugate `H ∘ P ∘ H^{∘-1}` of `P ∈ A` by a power series `H` over `O`, where `H^{∘-1}` is
the compositional inverse of `H` (`PowerSeries.compInv`). -/
@[expose] def conj (H : PowerSeries O) (P : CoefficientRing O) : CoefficientRing O :=
  subst (algebraMap (PowerSeries O) (CoefficientRing O) H.compInv)
    (subst P (algebraMap (PowerSeries O) (CoefficientRing O) H))

variable {H : PowerSeries O}

/-- Conjugation commutes with reduction modulo `𝔪 ^ (r + 1)`. -/
theorem reduction_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (r : ℕ)
    (P : CoefficientRing O) :
    reduction O r (conj H P) =
      LaurentSeries.conj (H.map (Truncation.mk O r)) (reduction O r P) := by
  rw [conj, reduction_subst, reduction_subst, reduction_algebraMap_powerSeries,
    reduction_algebraMap_powerSeries, PowerSeries.map_compInv _ hH hl]
  rfl

/-- Conjugation commutes with reduction to `κ((T))`. -/
theorem residue_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : CoefficientRing O) :
    residue O (conj H P) =
      LaurentSeries.conj (H.map (IsLocalRing.residue O)) (residue O P) := by
  rw [conj, residue_subst, residue_subst, residue_algebraMap_powerSeries,
    residue_algebraMap_powerSeries, PowerSeries.map_compInv _ hH hl]
  rfl

/-- If the image of an admissible `P ∈ A` in `κ((T))` is a power series `f`, then the image of
`H ∘ P ∘ H^{∘-1}` is `PowerSeries.conj` of `f` by the reduction of `H`. -/
theorem residue_conj_of_residue_eq (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : CoefficientRing O} (hP : IsAdmissible P) {f : PowerSeries (ResidueField O)}
    (hf : f.constantCoeff = 0) (hres : residue O P = HahnSeries.ofPowerSeries ℤ _ f) :
    residue O (conj H P) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.conj (H.map (IsLocalRing.residue O)) f) := by
  rw [residue_conj hH hl, hres, conj_ofPowerSeries hf
    (hres ▸ (isAdmissible_iff_isAdmissible_residue P).mp hP)]

/-- Conjugation preserves admissibility. -/
theorem IsAdmissible.conj {P : CoefficientRing O} (hP : IsAdmissible P)
    (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    IsAdmissible (CoefficientRing.conj H P) := by
  rw [isAdmissible_iff_isAdmissible_residue, residue_conj hH hl]
  exact LaurentSeries.IsAdmissible.conj ((isAdmissible_iff_isAdmissible_residue P).mp hP)
    (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)

/-- `H ∘ P ∘ H^{∘-1}` is the image of `H ∘ P` under the inverse of `f ↦ f(H)`. -/
theorem conj_eq_substEquiv_symm (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : CoefficientRing O) :
    conj H P = (substEquiv H).symm (subst P (algebraMap (PowerSeries O) (CoefficientRing O) H)) :=
  (substEquiv_symm_apply hH hl _).symm

/-- `(H ∘ P ∘ H^{∘-1}) ∘ H = H ∘ P`. -/
theorem subst_algebraMap_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P : CoefficientRing O) :
    subst (algebraMap (PowerSeries O) (CoefficientRing O) H) (conj H P) =
      subst P (algebraMap (PowerSeries O) (CoefficientRing O) H) := by
  rw [conj_eq_substEquiv_symm hH hl, ← substEquiv_apply hH hl, AlgEquiv.apply_symm_apply]

/-- `H ∘ P ∘ H^{∘-1} = Q` if and only if `H ∘ P = Q ∘ H`. -/
theorem conj_eq_iff_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P Q : CoefficientRing O} :
    conj H P = Q ↔ subst P (algebraMap (PowerSeries O) (CoefficientRing O) H) =
      subst (algebraMap (PowerSeries O) (CoefficientRing O) H) Q := by
  rw [conj_eq_substEquiv_symm hH hl, AlgEquiv.symm_apply_eq, substEquiv_apply hH hl]

/-- Conjugation fixes the variable. -/
theorem conj_X_right (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) : conj H X = X :=
  ext_reduction O fun r ↦ by
    rw [reduction_conj hH hl, reduction_X, LaurentSeries.conj_X_right
      (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)]

/-- Conjugation by the variable is the identity on admissible elements. -/
theorem conj_X {P : CoefficientRing O} (hP : IsAdmissible P) : conj PowerSeries.X P = P :=
  ext_reduction O fun r ↦ by
    rw [reduction_conj PowerSeries.constantCoeff_X
        (by rw [PowerSeries.coeff_one_X]; exact isUnit_one),
      PowerSeries.map_X, LaurentSeries.conj_X ((isAdmissible_iff_reduction r P).mp hP)]

/-- Substitution of `H ∘ P ∘ H^{∘-1}` is substitution of `P` conjugated by `f ↦ f(H)`. -/
theorem subst_conj_apply (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (P f : CoefficientRing O) :
    subst (conj H P) f = (substEquiv H).symm (subst P (substEquiv H f)) :=
  ext_reduction O fun r ↦ by
    rw [reduction_subst, reduction_conj hH hl, LaurentSeries.subst_conj_apply
      (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl),
      reduction_substEquiv_symm hH hl, reduction_subst, reduction_substEquiv hH hl]

theorem subst_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (P : CoefficientRing O) :
    subst (conj H P) =
      ((substEquiv H).symm.toAlgHom.comp (subst P)).comp (substEquiv H).toAlgHom :=
  AlgHom.ext (subst_conj_apply hH hl P)

/-- Conjugation preserves composition: `H ∘ (P ∘ G) ∘ H^{∘-1}` is the composite of
`H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`. -/
theorem conj_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {G P : CoefficientRing O} (hG : IsAdmissible G) (hP : IsAdmissible P) :
    conj H (subst G P) = subst (conj H G) (conj H P) :=
  ext_reduction O fun r ↦ by
    rw [reduction_conj hH hl, reduction_subst, reduction_subst, reduction_conj hH hl,
      reduction_conj hH hl, LaurentSeries.conj_subst (constantCoeff_map_eq_zero _ hH)
        (isUnit_coeff_one_map _ hl) ((isAdmissible_iff_reduction r G).mp hG)
        ((isAdmissible_iff_reduction r P).mp hP)]

/-- Conjugating by `H` and then by `H^{∘-1}` is the identity on admissible elements. -/
theorem conj_compInv_conj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : CoefficientRing O} (hP : IsAdmissible P) : conj H.compInv (conj H P) = P :=
  ext_reduction O fun r ↦ by
    rw [reduction_conj (PowerSeries.constantCoeff_compInv H)
        (PowerSeries.isUnit_coeff_one_compInv H), reduction_conj hH hl,
      PowerSeries.map_compInv _ hH hl, LaurentSeries.conj_compInv_conj
        (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)
        ((isAdmissible_iff_reduction r P).mp hP)]

/-- Conjugating by `H^{∘-1}` and then by `H` is the identity on admissible elements. -/
theorem conj_conj_compInv (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P : CoefficientRing O} (hP : IsAdmissible P) : conj H (conj H.compInv P) = P := by
  have h := conj_compInv_conj (PowerSeries.constantCoeff_compInv H)
    (PowerSeries.isUnit_coeff_one_compInv H) hP
  rwa [PowerSeries.compInv_compInv hH hl] at h

theorem conj_inj (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) {P G : CoefficientRing O}
    (hP : IsAdmissible P) (hG : IsAdmissible G) : conj H P = conj H G ↔ P = G :=
  ⟨fun h ↦ by rw [← conj_compInv_conj hH hl hP, h, conj_compInv_conj hH hl hG],
    fun h ↦ h ▸ rfl⟩

/-- Conjugation preserves and reflects commutation: `H ∘ P ∘ H^{∘-1}` and `H ∘ G ∘ H^{∘-1}`
commute if and only if `P` and `G` commute. -/
theorem conj_commute_iff (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    {P G : CoefficientRing O} (hP : IsAdmissible P) (hG : IsAdmissible G) :
    subst (conj H P) (conj H G) = subst (conj H G) (conj H P) ↔ subst P G = subst G P := by
  rw [← conj_subst hH hl hP hG, ← conj_subst hH hl hG hP,
    conj_inj hH hl (hG.subst hP) (hP.subst hG)]

end CoefficientRing

end FalseTateNonliftability
