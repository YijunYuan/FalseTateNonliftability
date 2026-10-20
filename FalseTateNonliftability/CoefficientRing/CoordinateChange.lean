/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.NormalizedDerivative

/-!
# Lifting coordinates and transporting commuting substitutions

Residue-field power-series coordinates lift to actual coordinates over the
original discrete valuation ring. Simultaneous coordinate conjugation on the
actual coefficient quotients preserves substitution and commutation, and its
compatible coordinates give the same laws on the canonical principal completion.

This supplies the coefficient-ring part of `nl:uniformizer-independence`.
The identification with coordinates of an actual field-of-norms action is
a separate producer.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- An actual residue coordinate lifts over the original DVR, with exactly
zero constant coefficient and an actual unit linear coefficient. -/
theorem exists_powerSeries_residue_coordinate
    (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    ∃ H : PowerSeries O, H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) ∧
      H.map (IsLocalRing.residue O) = w := by
  obtain ⟨H, hH⟩ := PowerSeries.map_surjective (IsLocalRing.residue O)
    IsLocalRing.residue_surjective w
  have hc : IsLocalRing.residue O H.constantCoeff = 0 := by
    have h := congrArg (fun f : PowerSeries (IsLocalRing.ResidueField O) ↦ f.coeff 0) hH
    simpa only [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hw] using h
  have hlinear : IsUnit (H.coeff 1) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have h := congrArg (fun f : PowerSeries (IsLocalRing.ResidueField O) ↦ f.coeff 1) hH
    change IsLocalRing.residue O (H.coeff 1) = w.coeff 1 at h
    exact h.trans_ne hwlinear.ne_zero
  refine ⟨H - PowerSeries.C H.constantCoeff, by simp, ?_, ?_⟩
  · simpa using hlinear
  · simpa only [map_sub, PowerSeries.map_C, hc, map_zero, sub_zero] using hH

variable (π : O) (hπ : Irreducible π)

/-- A coordinate over the DVR has the same actual residue through every
positive coefficient quotient. -/
theorem residue_map_quotient_powerSeries (r : ℕ) (hr : 1 ≤ r) (H : PowerSeries O) :
    (H.map (Ideal.Quotient.mk (Ideal.span {π ^ r}))).map (residue π hπ r hr) =
      H.map (IsLocalRing.residue O) := by
  ext n
  simp only [PowerSeries.coeff_map, residue_mk]

/-- Every actual residue coordinate has an actual coordinate lift in each
positive coefficient quotient. The lift is obtained over the original DVR. -/
theorem exists_truncated_residue_coordinate (r : ℕ) (hr : 1 ≤ r)
    (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    ∃ H : PowerSeries (Truncation π r), H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) ∧
      H.map (residue π hπ r hr) = w := by
  obtain ⟨H, hzero, hlinear, hres⟩ := exists_powerSeries_residue_coordinate w hw hwlinear
  refine ⟨H.map (Ideal.Quotient.mk _), ?_, ?_, ?_⟩
  · change Ideal.Quotient.mk _ H.constantCoeff = 0
    rw [hzero, map_zero]
  · simpa only [PowerSeries.coeff_map] using hlinear.map (Ideal.Quotient.mk _)
  · exact (residue_map_quotient_powerSeries π hπ r hr H).trans hres

/-- Actual coordinate conjugation preserves admissibility on the same
finite Laurent carrier. Both constituent substitutions are already defined. -/
theorem isAdmissible_coordinateConjugate (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    IsAdmissible (parameter π r) (coordinateConjugate π hπ r hr G hG H hzero hlinear) := by
  let := parameter_isMaximal π hπ r hr
  let hδ : IsNilpotent (parameter π r) := ⟨r, parameter_pow_eq_zero π r⟩
  have hH := isAdmissible_ofPowerSeries (parameter π r) H hzero hlinear
  have hQ := isAdmissible_ofPowerSeries (parameter π r) (H.substInvOfIsUnit hlinear)
    (PowerSeries.constantCoeff_substInvOfIsUnit H hlinear)
    (by rw [PowerSeries.coeff_one_substInvOfIsUnit]; exact Units.isUnit _)
  change IsAdmissible (parameter π r)
    ((powerSeriesSubstEquiv (parameter π r) hδ H hzero hlinear).symm
      (truncatedSubst π hπ r hr G hG (HahnSeries.ofPowerSeries ℤ _ H)))
  rw [powerSeriesSubstEquiv_symm_apply]
  exact (hH.substitution (parameter π r) hδ hG).substitution (parameter π r) hδ hQ

/-- Substitution at the actual coordinate conjugate is conjugation of the
actual substitution homomorphism, on every Laurent input. -/
theorem truncatedSubst_coordinateConjugate (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    let E : LaurentSeries (Truncation π r) ≃ₐ[Truncation π r]
        LaurentSeries (Truncation π r) := by
      let := parameter_isMaximal π hπ r hr
      exact powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ H hzero hlinear
    truncatedSubst π hπ r hr (coordinateConjugate π hπ r hr G hG H hzero hlinear)
      (isAdmissible_coordinateConjugate π hπ r hr G hG H hzero hlinear) =
        E.symm.toAlgHom.comp ((truncatedSubst π hπ r hr G hG).comp E.toAlgHom) := by
  let := parameter_isMaximal π hπ r hr
  let := orderTopology (Truncation π r)
  let hδ : IsNilpotent (parameter π r) := ⟨r, parameter_pow_eq_zero π r⟩
  dsimp only
  symm
  apply subst_unique (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩
  · exact (continuous_powerSeriesSubstEquiv_symm _ _ H hzero hlinear).comp
      ((continuous_subst _ _ G hG).comp
        (continuous_powerSeriesSubstEquiv _ _ H hzero hlinear))
  · change (powerSeriesSubstEquiv (parameter π r) hδ
      H hzero hlinear).symm
        (truncatedSubst π hπ r hr G hG
          (powerSeriesSubstEquiv (parameter π r) hδ H hzero hlinear
            (HahnSeries.single (1 : ℤ) 1))) = _
    rw [powerSeriesSubstEquiv_apply, subst_X]
    rfl

/-- Coordinate conjugation preserves the actual composition of admissible
parameters. This transports every prescribed composition identity. -/
theorem coordinateConjugate_substitution (r : ℕ) (hr : 1 ≤ r)
    (P G : LaurentSeries (Truncation π r))
    (hP : IsAdmissible (parameter π r) P) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    coordinateConjugate π hπ r hr (truncatedSubst π hπ r hr P hP G)
      (by let := parameter_isMaximal π hπ r hr
          exact hG.substitution (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ hP)
      H hzero hlinear =
    truncatedSubst π hπ r hr (coordinateConjugate π hπ r hr P hP H hzero hlinear)
      (isAdmissible_coordinateConjugate π hπ r hr P hP H hzero hlinear)
      (coordinateConjugate π hπ r hr G hG H hzero hlinear) := by
  let := parameter_isMaximal π hπ r hr
  let hδ : IsNilpotent (parameter π r) := ⟨r, parameter_pow_eq_zero π r⟩
  let E := powerSeriesSubstEquiv (parameter π r) hδ H hzero hlinear
  have hformula := AlgHom.congr_fun
    (truncatedSubst_coordinateConjugate π hπ r hr P hP H hzero hlinear)
    (coordinateConjugate π hπ r hr G hG H hzero hlinear)
  change truncatedSubst π hπ r hr (coordinateConjugate π hπ r hr P hP H hzero hlinear) _
      (coordinateConjugate π hπ r hr G hG H hzero hlinear) =
    E.symm (truncatedSubst π hπ r hr P hP
      (E (coordinateConjugate π hπ r hr G hG H hzero hlinear))) at hformula
  rw [hformula]
  change E.symm (truncatedSubst π hπ r hr (truncatedSubst π hπ r hr P hP G) _
      (HahnSeries.ofPowerSeries ℤ _ H)) =
    E.symm (truncatedSubst π hπ r hr P hP
      (E (coordinateConjugate π hπ r hr G hG H hzero hlinear)))
  apply congrArg E.symm
  rw [show E (coordinateConjugate π hπ r hr G hG H hzero hlinear) =
      truncatedSubst π hπ r hr G hG (HahnSeries.ofPowerSeries ℤ _ H) from
        coordinateConjugate_identity π hπ r hr G hG H hzero hlinear]
  exact (subst_assoc (parameter π r) hδ G P hG hP (HahnSeries.ofPowerSeries ℤ _ H)).symm

/-- The existing coordinate conjugation is injective on actual admissible
parameters. Agreement on the coordinate is extended using continuity. -/
theorem coordinateConjugate_injective (r : ℕ) (hr : 1 ≤ r)
    (P G : LaurentSeries (Truncation π r))
    (hP : IsAdmissible (parameter π r) P) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1))
    (heq : coordinateConjugate π hπ r hr P hP H hzero hlinear =
      coordinateConjugate π hπ r hr G hG H hzero hlinear) : P = G := by
  let := parameter_isMaximal π hπ r hr
  let := orderTopology (Truncation π r)
  have := orderTopology_t2Space (R := Truncation π r)
  let hδ : IsNilpotent (parameter π r) := ⟨r, parameter_pow_eq_zero π r⟩
  let E := powerSeriesSubstEquiv (parameter π r) hδ H hzero hlinear
  have hH : truncatedSubst π hπ r hr P hP (HahnSeries.ofPowerSeries ℤ _ H) =
      truncatedSubst π hπ r hr G hG (HahnSeries.ofPowerSeries ℤ _ H) := by
    rw [← coordinateConjugate_identity π hπ r hr P hP H hzero hlinear,
      ← coordinateConjugate_identity π hπ r hr G hG H hzero hlinear, heq]
  have hmaps : (truncatedSubst π hπ r hr P hP).comp E.toAlgHom =
      (truncatedSubst π hπ r hr G hG).comp E.toAlgHom := by
    apply continuous_algHom_ext_X
    · exact (continuous_subst _ hδ P hP).comp
        (continuous_powerSeriesSubstEquiv _ hδ H hzero hlinear)
    · exact (continuous_subst _ hδ G hG).comp
        (continuous_powerSeriesSubstEquiv _ hδ H hzero hlinear)
    · change truncatedSubst π hπ r hr P hP (E (HahnSeries.single (1 : ℤ) 1)) =
        truncatedSubst π hπ r hr G hG (E (HahnSeries.single (1 : ℤ) 1))
      have hEX : E (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ _ H :=
        subst_X (parameter π r) hδ _ _
      rw [hEX]
      exact hH
  have hx := AlgHom.congr_fun hmaps (E.symm (HahnSeries.single (1 : ℤ) 1))
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, E.apply_symm_apply,
    truncatedSubst_X] using hx

/-- Simultaneous actual coordinate conjugation preserves and reflects the
commutation identity. No group-law identities or transport certificate are assumed. -/
theorem coordinateConjugate_commute_iff (r : ℕ) (hr : 1 ≤ r)
    (P G : LaurentSeries (Truncation π r))
    (hP : IsAdmissible (parameter π r) P) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    truncatedSubst π hπ r hr (coordinateConjugate π hπ r hr P hP H hzero hlinear)
        (isAdmissible_coordinateConjugate π hπ r hr P hP H hzero hlinear)
        (coordinateConjugate π hπ r hr G hG H hzero hlinear) =
      truncatedSubst π hπ r hr (coordinateConjugate π hπ r hr G hG H hzero hlinear)
        (isAdmissible_coordinateConjugate π hπ r hr G hG H hzero hlinear)
        (coordinateConjugate π hπ r hr P hP H hzero hlinear) ↔
      truncatedSubst π hπ r hr P hP G = truncatedSubst π hπ r hr G hG P := by
  let := parameter_isMaximal π hπ r hr
  rw [← coordinateConjugate_substitution π hπ r hr P G hP hG H hzero hlinear,
    ← coordinateConjugate_substitution π hπ r hr G P hG hP H hzero hlinear]
  constructor
  · exact coordinateConjugate_injective π hπ r hr _ _ _ _ H hzero hlinear
  · intro heq
    simp only [heq]

/-- The actual coordinate automorphism commutes with every positive quotient
transition, on arbitrary Laurent inputs. -/
theorem factor_powerSeriesSubstEquiv {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) (f : LaurentSeries (Truncation π r)) :
    letI := parameter_isMaximal π hπ r (hs.trans hsr)
    letI := parameter_isMaximal π hπ s hs
    mapRingHom (factor π hsr)
        (powerSeriesSubstEquiv (parameter π r) ⟨r, parameter_pow_eq_zero π r⟩ H hzero hlinear f) =
      powerSeriesSubstEquiv (parameter π s) ⟨s, parameter_pow_eq_zero π s⟩ (H.map (factor π hsr))
        (by change factor π hsr H.constantCoeff = 0; rw [hzero, map_zero])
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (factor π hsr))
        (mapRingHom (factor π hsr) f) := by
  let := parameter_isMaximal π hπ r (hs.trans hsr)
  let := parameter_isMaximal π hπ s hs
  change mapRingHom (factor π hsr)
      (truncatedSubst π hπ r (hs.trans hsr) (HahnSeries.ofPowerSeries ℤ _ H) _ f) =
    truncatedSubst π hπ s hs (HahnSeries.ofPowerSeries ℤ _ (H.map (factor π hsr))) _
      (mapRingHom (factor π hsr) f)
  simpa only [mapRingHom_ofPowerSeries] using
    factor_truncatedSubst π hπ hsr hs (HahnSeries.ofPowerSeries ℤ _ H)
      (isAdmissible_ofPowerSeries _ H hzero hlinear) f

/-- Actual simultaneous conjugation is compatible with all positive
coefficient transitions, using the same original quotient maps. -/
theorem factor_coordinateConjugate {s r : ℕ} (hsr : s ≤ r) (hs : 1 ≤ s)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    mapRingHom (factor π hsr)
      (coordinateConjugate π hπ r (hs.trans hsr) G hG H hzero hlinear) =
    coordinateConjugate π hπ s hs (mapRingHom (factor π hsr) G)
      ((isAdmissible_factor_iff π hπ hsr hs G).mpr hG) (H.map (factor π hsr))
      (by change factor π hsr H.constantCoeff = 0; rw [hzero, map_zero])
      (by simpa only [PowerSeries.coeff_map] using hlinear.map (factor π hsr)) := by
  let := parameter_isMaximal π hπ r (hs.trans hsr)
  let := parameter_isMaximal π hπ s hs
  let q := factor π hsr
  let Hs := H.map q
  have hz : Hs.constantCoeff = 0 := by change q H.constantCoeff = 0; rw [hzero, map_zero]
  have hl : IsUnit (Hs.coeff 1) := by
    simpa only [Hs, PowerSeries.coeff_map] using hlinear.map q
  let E := powerSeriesSubstEquiv (parameter π s) ⟨s, parameter_pow_eq_zero π s⟩ Hs hz hl
  apply E.injective
  change E (mapRingHom q (coordinateConjugate π hπ r (hs.trans hsr) G hG H hzero hlinear)) =
    E (coordinateConjugate π hπ s hs (mapRingHom q G) _ Hs hz hl)
  rw [show E (coordinateConjugate π hπ s hs (mapRingHom q G) _ Hs hz hl) =
      truncatedSubst π hπ s hs (mapRingHom q G) _ (HahnSeries.ofPowerSeries ℤ _ Hs) from
        coordinateConjugate_identity π hπ s hs _ _ Hs hz hl]
  calc
    E (mapRingHom q (coordinateConjugate π hπ r (hs.trans hsr) G hG H hzero hlinear)) =
        mapRingHom q (truncatedSubst π hπ r (hs.trans hsr) (HahnSeries.ofPowerSeries ℤ _ H)
          (isAdmissible_ofPowerSeries _ H hzero hlinear)
          (coordinateConjugate π hπ r (hs.trans hsr) G hG H hzero hlinear)) :=
      (factor_powerSeriesSubstEquiv π hπ hsr hs H hzero hlinear _).symm
    _ = mapRingHom q (truncatedSubst π hπ r (hs.trans hsr) G hG
        (HahnSeries.ofPowerSeries ℤ _ H)) :=
      congrArg (mapRingHom q)
        (coordinateConjugate_identity π hπ r (hs.trans hsr) G hG H hzero hlinear)
    _ = _ := by rw [factor_truncatedSubst, mapRingHom_ofPowerSeries]

/-- On the same canonical completion, the explicit conjugated element has
exactly the already constructed finite coordinate conjugates. -/
theorem completedPrincipalReduction_coordinateConjugate
    (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1))
    (r : ℕ) (hr : 1 ≤ r) :
    completedPrincipalReduction π r
      ((completedPowerSeriesSubstEquiv π hπ H hzero hlinear).symm
        (completedSubst π hπ G hG (completedPowerSeries π H))) =
    coordinateConjugate π hπ r hr (completedPrincipalReduction π r G)
      ((completedIsAdmissible_iff π hπ r hr G).mp hG)
      (H.map (Ideal.Quotient.mk (Ideal.span {π ^ r})))
      (by change Ideal.Quotient.mk _ H.constantCoeff = 0; rw [hzero, map_zero])
      (by simpa only [PowerSeries.coeff_map] using
        hlinear.map (Ideal.Quotient.mk (Ideal.span {π ^ r}))) := by
  let := parameter_isMaximal π hπ r hr
  rw [completedPrincipalReduction_powerSeriesSubstEquiv_symm π hπ H hzero hlinear r hr,
    completedPrincipalReduction_completedSubst π hπ G hG r hr,
    completedPrincipalReduction_powerSeries]
  rfl

/-- The explicit conjugated element in the original completion is admissible;
its positive coordinates are the actual finite conjugates. -/
theorem completedIsAdmissible_coordinateConjugate
    (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    CompletedIsAdmissible π hπ
      ((completedPowerSeriesSubstEquiv π hπ H hzero hlinear).symm
        (completedSubst π hπ G hG (completedPowerSeries π H))) := by
  rw [completedIsAdmissible_iff π hπ 1 le_rfl,
    completedPrincipalReduction_coordinateConjugate π hπ G hG H hzero hlinear 1 le_rfl]
  exact isAdmissible_coordinateConjugate π hπ 1 le_rfl _ _ _ _ _

/-- Actual substitution on the same completion conjugates by the actual
coordinate automorphism. Equality is proved in every positive coordinate,
without inferring uniqueness from adic continuity and the variable alone. -/
theorem completedSubst_coordinateConjugate
    (G : PrincipalCompletion π) (hG : CompletedIsAdmissible π hπ G)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    let E := completedPowerSeriesSubstEquiv π hπ H hzero hlinear
    completedSubst π hπ (E.symm (completedSubst π hπ G hG (completedPowerSeries π H)))
      (completedIsAdmissible_coordinateConjugate π hπ G hG H hzero hlinear) =
        E.symm.toAlgHom.comp ((completedSubst π hπ G hG).comp E.toAlgHom) := by
  dsimp only
  apply AlgHom.ext
  intro f
  apply completedPrincipalReduction_ext_pos π
  intro r hr
  let := parameter_isMaximal π hπ r hr
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    completedPrincipalReduction_completedSubst π hπ _ _ r hr,
    completedPrincipalReduction_coordinateConjugate π hπ G hG H hzero hlinear r hr,
    completedPrincipalReduction_powerSeriesSubstEquiv_symm π hπ H hzero hlinear r hr,
    completedPrincipalReduction_powerSeriesSubstEquiv π hπ H hzero hlinear r hr]
  exact AlgHom.congr_fun
    (truncatedSubst_coordinateConjugate π hπ r hr (completedPrincipalReduction π r G)
      ((completedIsAdmissible_iff π hπ r hr G).mp hG)
      (H.map (Ideal.Quotient.mk (Ideal.span {π ^ r}))) _ _) (completedPrincipalReduction π r f)

/-- Simultaneous conjugation preserves and reflects actual completed
commutation. The proof descends to each original positive coefficient quotient. -/
theorem completed_coordinateConjugate_commute_iff
    (P G : PrincipalCompletion π)
    (hP : CompletedIsAdmissible π hπ P) (hG : CompletedIsAdmissible π hπ G)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    let E := completedPowerSeriesSubstEquiv π hπ H hzero hlinear
    let PH := E.symm (completedSubst π hπ P hP (completedPowerSeries π H))
    let GH := E.symm (completedSubst π hπ G hG (completedPowerSeries π H))
    completedSubst π hπ PH (completedIsAdmissible_coordinateConjugate π hπ P hP H hzero hlinear) GH =
      completedSubst π hπ GH (completedIsAdmissible_coordinateConjugate π hπ G hG H hzero hlinear) PH ↔
    completedSubst π hπ P hP G = completedSubst π hπ G hG P := by
  dsimp only
  constructor <;> intro heq
  · apply completedPrincipalReduction_ext_pos π
    intro r hr
    have hfinite := congrArg (completedPrincipalReduction π r) heq
    simp only [completedPrincipalReduction_completedSubst π hπ _ _ r hr,
      completedPrincipalReduction_coordinateConjugate π hπ P hP H hzero hlinear r hr,
      completedPrincipalReduction_coordinateConjugate π hπ G hG H hzero hlinear r hr] at hfinite
    rw [completedPrincipalReduction_completedSubst π hπ P hP r hr,
      completedPrincipalReduction_completedSubst π hπ G hG r hr]
    exact (coordinateConjugate_commute_iff π hπ r hr _ _ _ _ _ _ _).mp hfinite
  · apply completedPrincipalReduction_ext_pos π
    intro r hr
    have hfinite := congrArg (completedPrincipalReduction π r) heq
    simp only [completedPrincipalReduction_completedSubst π hπ _ _ r hr] at hfinite
    simp only [completedPrincipalReduction_completedSubst π hπ _ _ r hr,
      completedPrincipalReduction_coordinateConjugate π hπ P hP H hzero hlinear r hr,
      completedPrincipalReduction_coordinateConjugate π hπ G hG H hzero hlinear r hr]
    exact (coordinateConjugate_commute_iff π hπ r hr _ _ _ _ _ _ _).mpr hfinite

local instance coordinateChangeResidueZeroSpanIsMaximal :
    (Ideal.span ({(0 : IsLocalRing.ResidueField O)} : Set (IsLocalRing.ResidueField O))).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The actual conjugated parameter reduces to the same coordinate conjugate
over the original residue field, for any admissible parameter. -/
theorem residue_coordinateConjugate_apply (r : ℕ) (hr : 1 ≤ r)
    (G : LaurentSeries (Truncation π r)) (hG : IsAdmissible (parameter π r) G)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    mapRingHom (residue π hπ r hr) (coordinateConjugate π hπ r hr G hG H hzero hlinear) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero (H.map (residue π hπ r hr))
        (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero])
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (residue π hπ r hr))).symm
        (subst 0 IsNilpotent.zero (mapRingHom (residue π hπ r hr) G)
          (isAdmissible_residue π hπ r hr G hG)
          (HahnSeries.ofPowerSeries ℤ _ (H.map (residue π hπ r hr)))) := by
  let := parameter_isMaximal π hπ r hr
  let q := residue π hπ r hr
  let Hbar := H.map q
  have hz : Hbar.constantCoeff = 0 := by
    change q H.constantCoeff = 0
    rw [hzero, map_zero]
  have hl : IsUnit (Hbar.coeff 1) := by
    simpa only [Hbar, PowerSeries.coeff_map] using hlinear.map q
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero Hbar hz hl
  apply E.injective
  change E (mapRingHom q (coordinateConjugate π hπ r hr G hG H hzero hlinear)) =
    E (E.symm _)
  rw [E.apply_symm_apply]
  calc
    E (mapRingHom q (coordinateConjugate π hπ r hr G hG H hzero hlinear)) =
        mapRingHom q (truncatedSubst π hπ r hr (HahnSeries.ofPowerSeries ℤ _ H)
          (isAdmissible_ofPowerSeries _ H hzero hlinear)
          (coordinateConjugate π hπ r hr G hG H hzero hlinear)) :=
      (residue_powerSeriesSubstEquiv π hπ r hr H hzero hlinear _).symm
    _ = mapRingHom q (truncatedSubst π hπ r hr G hG (HahnSeries.ofPowerSeries ℤ _ H)) :=
      congrArg (mapRingHom q) (coordinateConjugate_identity π hπ r hr G hG H hzero hlinear)
    _ = _ := by rw [residue_truncatedSubst, mapRingHom_ofPowerSeries]

end FalseTateNonliftability.CoefficientRing
