module

public import FalseTateNonliftability.CoefficientRing.CoordinateChange
public import FalseTateNonliftability.FieldOfNorms.Liftability
public import FontaineWintenberger.FieldOfNorms.LaurentCoordinates
public import FontaineWintenberger.LocalField.LaurentSubstitution
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Lifts and original norm-field uniformizers

Full finite and completed lift families transport under actual coordinate
changes. Original norm-field evaluation maps supply the coordinate changes.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

section FiniteResidue

variable (k : Type*) [Field k] [Finite k]

local instance coordinateLiftZeroSpanIsMaximal :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The actual residue-cardinality monomial has positive order. -/
theorem cardMonomial_isAdmissible :
    IsAdmissible (0 : k) (HahnSeries.single (Nat.card k : ℤ) (1 : k)) := by
  rw [isAdmissible_zero_iff]
  exact ⟨Nat.card k, by exact_mod_cast (Finite.card_pos (α := k)),
    HahnSeries.orderTop_single one_ne_zero⟩

/-- Over any finite coefficient field, substitution at the actual
residue-cardinality monomial is the genuine cardinality Frobenius. -/
theorem subst_cardMonomial_eq_pow (A : LaurentSeries k) :
    subst 0 IsNilpotent.zero (HahnSeries.single (Nat.card k : ℤ) 1)
      (cardMonomial_isAdmissible k) A = A ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  let := orderTopology k
  let := orderTopology_isTopologicalRing (R := k)
  let := orderTopology_t2Space (R := k)
  let F := FiniteField.frobeniusAlgHom k (LaurentSeries k)
  have hF : Continuous F := by
    change Continuous (fun A : LaurentSeries k => A ^ Fintype.card k)
    exact continuous_pow _
  have hX : F (HahnSeries.single (1 : ℤ) (1 : k)) =
      HahnSeries.single (Nat.card k : ℤ) 1 := by
    change (HahnSeries.single (1 : ℤ) (1 : k)) ^ Fintype.card k = _
    simp only [HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow,
      Nat.card_eq_fintype_card]
  have heq := congrArg (fun E : LaurentSeries k →ₐ[k] LaurentSeries k => E A)
    (subst_unique 0 IsNilpotent.zero _ (cardMonomial_isAdmissible k) F hF hX).symm
  change subst 0 IsNilpotent.zero (HahnSeries.single (Nat.card k : ℤ) 1)
    (cardMonomial_isAdmissible k) A = A ^ Fintype.card k at heq
  simpa only [Nat.card_eq_fintype_card] using heq

end FiniteResidue

section CompletedConjugation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π : O) (hπ : Irreducible π)

local instance coordinateLiftResidueZeroSpanIsMaximal :
    (Ideal.span ({(0 : IsLocalRing.ResidueField O)} : Set (IsLocalRing.ResidueField O))).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The actual coordinate conjugate on the original principal completion. -/
def completedCoordinateConjugate (G : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) (H : PowerSeries O)
    (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    PrincipalCompletion π :=
  (completedPowerSeriesSubstEquiv π hπ H hzero hlinear).symm
    (completedSubst π hπ G hG (completedPowerSeries π H))

/-- The actual completed coordinate conjugate is admissible. -/
theorem completedIsAdmissible_completedCoordinateConjugate (G : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) (H : PowerSeries O)
    (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    CompletedIsAdmissible π hπ
      (completedCoordinateConjugate π hπ G hG H hzero hlinear) :=
  completedIsAdmissible_coordinateConjugate π hπ G hG H hzero hlinear

/-- Coordinate conjugation transports actual composition on the whole
completion, by its already proved identities in every positive quotient. -/
theorem completedCoordinateConjugate_substitution (G J : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) (hJ : CompletedIsAdmissible π hπ J)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    completedCoordinateConjugate π hπ (completedSubst π hπ G hG J)
        (hJ.substitution π hπ hG) H hzero hlinear =
      completedSubst π hπ (completedCoordinateConjugate π hπ G hG H hzero hlinear)
        (completedIsAdmissible_completedCoordinateConjugate π hπ G hG H hzero hlinear)
        (completedCoordinateConjugate π hπ J hJ H hzero hlinear) := by
  apply completedPrincipalReduction_ext_pos π
  intro r hr
  let := parameter_isMaximal π hπ r hr
  let Hr := H.map (Ideal.Quotient.mk (Ideal.span {π ^ r}))
  have hz : Hr.constantCoeff = 0 := by
    change Ideal.Quotient.mk _ H.constantCoeff = 0
    rw [hzero, map_zero]
  have hl : IsUnit (Hr.coeff 1) := by
    simpa only [Hr, PowerSeries.coeff_map] using
      hlinear.map (Ideal.Quotient.mk (Ideal.span {π ^ r}))
  have hred (Y : PrincipalCompletion π) (hY : CompletedIsAdmissible π hπ Y) :
      completedPrincipalReduction π r
          (completedCoordinateConjugate π hπ Y hY H hzero hlinear) =
        coordinateConjugate π hπ r hr (completedPrincipalReduction π r Y)
          ((completedIsAdmissible_iff π hπ r hr Y).mp hY) Hr hz hl :=
    completedPrincipalReduction_coordinateConjugate π hπ Y hY H hzero hlinear r hr
  have hsubst (Y : PrincipalCompletion π) (hY : CompletedIsAdmissible π hπ Y)
      (Z : PrincipalCompletion π) :
      completedPrincipalReduction π r (completedSubst π hπ Y hY Z) =
        truncatedSubst π hπ r hr (completedPrincipalReduction π r Y)
          ((completedIsAdmissible_iff π hπ r hr Y).mp hY)
          (completedPrincipalReduction π r Z) :=
    completedPrincipalReduction_completedSubst π hπ Y hY r hr Z
  simp only [hred, hsubst]
  exact coordinateConjugate_substitution π hπ r hr
    (completedPrincipalReduction π r G) (completedPrincipalReduction π r J)
    ((completedIsAdmissible_iff π hπ r hr G).mp hG)
    ((completedIsAdmissible_iff π hπ r hr J).mp hJ)
    Hr hz hl

/-- Completed coordinate conjugation reduces to conjugation over the actual
residue field, with no restriction on the Laurent input. -/
theorem completedResidue_completedCoordinateConjugate (G : PrincipalCompletion π)
    (hG : CompletedIsAdmissible π hπ G) (H : PowerSeries O)
    (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    completedResidue π hπ (completedCoordinateConjugate π hπ G hG H hzero hlinear) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero (H.map (IsLocalRing.residue O))
        (by change IsLocalRing.residue O H.constantCoeff = 0; rw [hzero, map_zero])
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (IsLocalRing.residue O))).symm
        (subst 0 IsNilpotent.zero (completedResidue π hπ G)
          (by rw [isAdmissible_zero_iff]; exact hG)
          (HahnSeries.ofPowerSeries ℤ _ (H.map (IsLocalRing.residue O)))) := by
  rw [completedResidue_eq π hπ 1 le_rfl,
    show completedPrincipalReduction π 1
        (completedCoordinateConjugate π hπ G hG H hzero hlinear) = _ from
      completedPrincipalReduction_coordinateConjugate π hπ G hG H hzero hlinear 1 le_rfl,
    residue_coordinateConjugate_apply]
  simp only [residue_map_quotient_powerSeries]
  rfl

/-- The genuine residue Frobenius is unchanged by every actual coordinate
change, over any finite residue field. -/
theorem completedCoordinateConjugate_residue_card_monomial
    [Finite (IsLocalRing.ResidueField O)] (P : PrincipalCompletion π)
    (hP : completedResidue π hπ P =
      HahnSeries.single (Nat.card (IsLocalRing.ResidueField O) : ℤ) 1)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    completedResidue π hπ
        (completedCoordinateConjugate π hπ P
          (completedIsAdmissible_of_residue_card_monomial π hπ P hP) H hzero hlinear) =
      HahnSeries.single (Nat.card (IsLocalRing.ResidueField O) : ℤ) 1 := by
  rw [completedResidue_completedCoordinateConjugate]
  simp only [hP]
  rw [subst_cardMonomial_eq_pow, map_pow]
  have hX : (powerSeriesSubstEquiv 0 IsNilpotent.zero (H.map (IsLocalRing.residue O))
      (by change IsLocalRing.residue O H.constantCoeff = 0; rw [hzero, map_zero])
      (by simpa only [PowerSeries.coeff_map] using hlinear.map (IsLocalRing.residue O))).symm
        (HahnSeries.ofPowerSeries ℤ _ (H.map (IsLocalRing.residue O))) =
      HahnSeries.single (1 : ℤ) 1 := by
    apply (powerSeriesSubstEquiv 0 IsNilpotent.zero (H.map (IsLocalRing.residue O))
      (by change IsLocalRing.residue O H.constantCoeff = 0; rw [hzero, map_zero])
      (by simpa only [PowerSeries.coeff_map] using hlinear.map (IsLocalRing.residue O))).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (subst_X 0 IsNilpotent.zero _ _).symm
  rw [hX]
  simp only [HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow]

/-- The full completed conjugate has the actual conjugated residue
power-series coordinate. -/
theorem completedCoordinateConjugate_residue_powerSeries (G : PrincipalCompletion π)
    (f : PowerSeries (IsLocalRing.ResidueField O)) (hf : f.constantCoeff = 0)
    (hflinear : IsUnit (f.coeff 1))
    (hres : completedResidue π hπ G = HahnSeries.ofPowerSeries ℤ _ f)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    completedResidue π hπ
        (completedCoordinateConjugate π hπ G
          (completedIsAdmissible_of_residue_powerSeries π hπ G f hf hflinear hres)
          H hzero hlinear) =
      HahnSeries.ofPowerSeries ℤ _
        (powerSeriesConjugate f (H.map (IsLocalRing.residue O))
          (by simpa only [PowerSeries.coeff_map] using hlinear.map (IsLocalRing.residue O))) := by
  rw [completedResidue_completedCoordinateConjugate]
  simp only [hres]
  exact (ofPowerSeries_powerSeriesConjugate f _ hf hflinear
    (by change IsLocalRing.residue O H.constantCoeff = 0; rw [hzero, map_zero])
    (by simpa only [PowerSeries.coeff_map] using hlinear.map (IsLocalRing.residue O))).symm

variable [Finite (IsLocalRing.ResidueField O)] {Γ : Type*} [Group Γ]
  (f : Γ → PowerSeries (IsLocalRing.ResidueField O))
  (hfzero : ∀ g, (f g).constantCoeff = 0) (hflinear : ∀ g, IsUnit ((f g).coeff 1))

namespace CompletedLift

/-- An actual integral coordinate change transports all completed lifting
data at once, including the reversed law for the entire group family. -/
def conjugate (L : CompletedLift π hπ f hfzero hflinear)
    (H : PowerSeries O) (hzero : H.constantCoeff = 0) (hlinear : IsUnit (H.coeff 1)) :
    CompletedLift π hπ
      (fun g ↦ powerSeriesConjugate (f g) (H.map (IsLocalRing.residue O))
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (IsLocalRing.residue O)))
      (fun g ↦ constantCoeff_powerSeriesConjugate (f g) _ (hfzero g)
        (by change IsLocalRing.residue O H.constantCoeff = 0; rw [hzero, map_zero]) _)
      (fun g ↦ isUnit_linear_powerSeriesConjugate (f g) _ (hfzero g) (hflinear g)
        (by change IsLocalRing.residue O H.constantCoeff = 0; rw [hzero, map_zero]) _) where
  P := completedCoordinateConjugate π hπ L.P
    (completedIsAdmissible_of_residue_card_monomial π hπ L.P L.residue_P) H hzero hlinear
  F g := completedCoordinateConjugate π hπ (L.F g)
    (completedIsAdmissible_of_residue_powerSeries π hπ (L.F g) (f g)
      (hfzero g) (hflinear g) (L.residue_F g)) H hzero hlinear
  residue_P := completedCoordinateConjugate_residue_card_monomial π hπ L.P L.residue_P
    H hzero hlinear
  residue_F g := completedCoordinateConjugate_residue_powerSeries π hπ (L.F g) (f g)
    (hfzero g) (hflinear g) (L.residue_F g) H hzero hlinear
  commute g := (completed_coordinateConjugate_commute_iff π hπ L.P (L.F g) _ _
    H hzero hlinear).mpr (L.commute g)
  composition g h := by
    rw [← completedCoordinateConjugate_substitution]
    simp only [L.composition g h]

end CompletedLift

/-- Every actual residue coordinate can be lifted over the original DVR,
so the whole-family lifting condition transports under any such coordinate. -/
theorem Liftable.coordinateChange (hL : Liftable π hπ f hfzero hflinear)
    (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    Liftable π hπ (fun g ↦ powerSeriesConjugate (f g) w hwlinear)
      (fun g ↦ constantCoeff_powerSeriesConjugate (f g) w (hfzero g) hw hwlinear)
      (fun g ↦ isUnit_linear_powerSeriesConjugate (f g) w (hfzero g) (hflinear g) hw hwlinear) := by
  obtain ⟨H, hzero, hlinear, hres⟩ := exists_powerSeries_residue_coordinate w hw hwlinear
  obtain ⟨L⟩ := hL
  have LC := L.conjugate π hπ f hfzero hflinear H hzero hlinear
  subst w
  exact ⟨LC⟩

/-- Liftability is invariant under every actual residue coordinate change.
The converse transports through the genuine inverse power-series coordinate. -/
theorem liftable_coordinateChange_iff
    (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    Liftable π hπ (fun g ↦ powerSeriesConjugate (f g) w hwlinear)
        (fun g ↦ constantCoeff_powerSeriesConjugate (f g) w (hfzero g) hw hwlinear)
        (fun g ↦ isUnit_linear_powerSeriesConjugate (f g) w (hfzero g) (hflinear g) hw hwlinear) ↔
      Liftable π hπ f hfzero hflinear := by
  constructor
  · intro hL
    have hi : IsUnit ((w.substInvOfIsUnit hwlinear).coeff 1) := by
      rw [PowerSeries.coeff_one_substInvOfIsUnit]
      exact Units.isUnit _
    have hback := hL.coordinateChange π hπ _ _ _ (w.substInvOfIsUnit hwlinear)
      (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear) hi
    convert hback using 1
    funext g
    rw [powerSeriesConjugate_powerSeriesConjugate (f g) w _ (hfzero g) (hflinear g)
      hw hwlinear (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear) hi]
    have hcoordinate (v : PowerSeries (IsLocalRing.ResidueField O))
        (hv : IsUnit (v.coeff 1)) (heq : v = PowerSeries.X) :
        powerSeriesConjugate (f g) v hv = f g := by
      subst v
      exact powerSeriesConjugate_X (f g) (hfzero g)
    exact (hcoordinate _ _ (PowerSeries.subst_substInvOfIsUnit_left w hw hwlinear)).symm
  · exact fun hL ↦ hL.coordinateChange π hπ f hfzero hflinear w hw hwlinear

end CompletedConjugation

section FiniteConjugation

attribute [local instance] coordinateLiftResidueZeroSpanIsMaximal

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π : O) (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField O)]
  {Γ : Type*} [Group Γ]
  (f : Γ → PowerSeries (IsLocalRing.ResidueField O))
  (hfzero : ∀ g, (f g).constantCoeff = 0) (hflinear : ∀ g, IsUnit ((f g).coeff 1))
  (r : ℕ) (hr : 1 ≤ r)

namespace FiniteLift

/-- The identical simultaneous conjugation transports all actual finite
lifting data, without requiring a lift to the completion. -/
def conjugate (L : FiniteLift π hπ f hfzero hflinear r hr)
    (H : PowerSeries (Truncation π r)) (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) :
    FiniteLift π hπ
      (fun g ↦ powerSeriesConjugate (f g) (H.map (residue π hπ r hr))
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (residue π hπ r hr)))
      (fun g ↦ constantCoeff_powerSeriesConjugate (f g) _ (hfzero g)
        (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero]) _)
      (fun g ↦ isUnit_linear_powerSeriesConjugate (f g) _ (hfzero g) (hflinear g)
        (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero]) _) r hr := by
  let := parameter_isMaximal π hπ r hr
  let hP := isAdmissible_of_residue_card_monomial π hπ r hr L.P L.residue_P
  let hF (g : Γ) := isAdmissible_of_residue_powerSeries π hπ r hr (L.F g) (f g)
    (hfzero g) (hflinear g) (L.residue_F g)
  refine { P := coordinateConjugate π hπ r hr L.P hP H hzero hlinear
           F := fun g ↦ coordinateConjugate π hπ r hr (L.F g) (hF g) H hzero hlinear
           residue_P := ?_
           residue_F := ?_
           commute := ?_
           composition := ?_ }
  · rw [residue_coordinateConjugate_apply]
    simp only [L.residue_P]
    rw [subst_cardMonomial_eq_pow, map_pow]
    have hX : (powerSeriesSubstEquiv 0 IsNilpotent.zero (H.map (residue π hπ r hr))
        (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero])
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (residue π hπ r hr))).symm
          (HahnSeries.ofPowerSeries ℤ _ (H.map (residue π hπ r hr))) =
        HahnSeries.single (1 : ℤ) 1 := by
      apply (powerSeriesSubstEquiv 0 IsNilpotent.zero (H.map (residue π hπ r hr))
        (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero])
        (by simpa only [PowerSeries.coeff_map] using hlinear.map (residue π hπ r hr))).injective
      rw [AlgEquiv.apply_symm_apply]
      exact (subst_X 0 IsNilpotent.zero _ _).symm
    rw [hX]
    simp only [HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow]
  · intro g
    rw [residue_coordinateConjugate_apply]
    simp only [L.residue_F g]
    exact (ofPowerSeries_powerSeriesConjugate (f g) _ (hfzero g) (hflinear g)
      (by change residue π hπ r hr H.constantCoeff = 0; rw [hzero, map_zero])
      (by simpa only [PowerSeries.coeff_map] using hlinear.map (residue π hπ r hr))).symm
  · intro g
    exact (coordinateConjugate_commute_iff π hπ r hr L.P (L.F g) hP (hF g)
      H hzero hlinear).mpr (L.commute g)
  · intro g h
    rw [← coordinateConjugate_substitution]
    simp only [L.composition g h]

end FiniteLift

/-- Finite liftability transports under every actual residue coordinate,
at the same positive coefficient level. -/
theorem FiniteLiftable.coordinateChange
    (hL : FiniteLiftable π hπ f hfzero hflinear r hr)
    (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    FiniteLiftable π hπ (fun g ↦ powerSeriesConjugate (f g) w hwlinear)
      (fun g ↦ constantCoeff_powerSeriesConjugate (f g) w (hfzero g) hw hwlinear)
      (fun g ↦ isUnit_linear_powerSeriesConjugate (f g) w (hfzero g) (hflinear g) hw hwlinear) r hr := by
  obtain ⟨H, hzero, hlinear, hres⟩ := exists_truncated_residue_coordinate π hπ r hr w hw hwlinear
  obtain ⟨L⟩ := hL
  have LC := L.conjugate π hπ f hfzero hflinear r hr H hzero hlinear
  subst w
  exact ⟨LC⟩

/-- At each original positive quotient, full-family finite liftability is
independent of the actual invertible residue coordinate. -/
theorem finiteLiftable_coordinateChange_iff
    (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
    (hwlinear : IsUnit (w.coeff 1)) :
    FiniteLiftable π hπ (fun g ↦ powerSeriesConjugate (f g) w hwlinear)
        (fun g ↦ constantCoeff_powerSeriesConjugate (f g) w (hfzero g) hw hwlinear)
        (fun g ↦ isUnit_linear_powerSeriesConjugate (f g) w (hfzero g) (hflinear g) hw hwlinear) r hr ↔
      FiniteLiftable π hπ f hfzero hflinear r hr := by
  constructor
  · intro hL
    have hi : IsUnit ((w.substInvOfIsUnit hwlinear).coeff 1) := by
      rw [PowerSeries.coeff_one_substInvOfIsUnit]
      exact Units.isUnit _
    have hback := hL.coordinateChange π hπ _ _ _ r hr (w.substInvOfIsUnit hwlinear)
      (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear) hi
    convert hback using 1
    funext g
    rw [powerSeriesConjugate_powerSeriesConjugate (f g) w _ (hfzero g) (hflinear g)
      hw hwlinear (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear) hi]
    have hcoordinate (v : PowerSeries (IsLocalRing.ResidueField O))
        (hv : IsUnit (v.coeff 1)) (heq : v = PowerSeries.X) :
        powerSeriesConjugate (f g) v hv = f g := by
      subst v
      exact powerSeriesConjugate_X (f g) (hfzero g)
    exact (hcoordinate _ _ (PowerSeries.subst_substInvOfIsUnit_left w hw hwlinear)).symm
  · exact fun hL ↦ hL.coordinateChange π hπ f hfzero hflinear r hr w hw hwlinear

end FiniteConjugation

section ValuedCoordinates

open WithZero
open scoped LaurentSeries

variable {k : Type*} [Field k]

/-- The actual coordinate intertwining equation identifies the ordinary
conjugate, using the genuine formal inverse coordinate. -/
theorem powerSeriesConjugate_eq_of_intertwining (f h w : PowerSeries k)
    (hw : w.constantCoeff = 0) (hwlinear : IsUnit (w.coeff 1))
    (heq : PowerSeries.subst f w = PowerSeries.subst w h) :
    powerSeriesConjugate f w hwlinear = h := by
  change PowerSeries.subst (w.substInvOfIsUnit hwlinear) (PowerSeries.subst f w) = h
  rw [heq, PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hw)
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      (PowerSeries.constantCoeff_substInvOfIsUnit w hwlinear)),
    PowerSeries.subst_substInvOfIsUnit_right w hw hwlinear, PowerSeries.X_subst]

/-- A coefficient-fixing valued Laurent isomorphism is ordinary
substitution on every power-series input at its actual parameter image. -/
theorem exists_coordinateChange_of_valuedEquiv (F : LaurentSeries k ≃+* LaurentSeries k)
    (hv : ∀ A : LaurentSeries k, (Valued.v (F A) : WithZero (Multiplicative ℤ)) = Valued.v A)
    (hC : ∀ a : k, F (HahnSeries.C a) = HahnSeries.C a) :
    ∃ w : PowerSeries k, (w : LaurentSeries k) = F (HahnSeries.single (1 : ℤ) 1) ∧
      w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) ∧
        ∀ A : PowerSeries k, F (A : LaurentSeries k) = (A.subst w : LaurentSeries k) := by
  have hX : (Valued.v (F (HahnSeries.single (1 : ℤ) (1 : k))) :
      WithZero (Multiplicative ℤ)) = exp (-1 : ℤ) := by
    rw [hv]
    simpa using LaurentSeries.valuation_X_pow k 1
  obtain ⟨w, hw, hzero, hlinear⟩ := exists_powerSeries_coordinate_of_valuation _ hX
  refine ⟨w, hw, hzero, hlinear, ?_⟩
  intro A
  exact FontaineWintenberger.map_ofPowerSeries_eq_subst F.toRingHom
    (FontaineWintenberger.valuedRingEquiv_uniformContinuous F hv).continuous
    hC w hzero hw.symm A

end ValuedCoordinates

section Intertwining

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π : O) (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField O)]
  {Γ : Type*} [Group Γ]
  (f h : Γ → PowerSeries (IsLocalRing.ResidueField O))
  (hfzero : ∀ g, (f g).constantCoeff = 0) (hflinear : ∀ g, IsUnit ((f g).coeff 1))
  (hhzero : ∀ g, (h g).constantCoeff = 0) (hhlinear : ∀ g, IsUnit ((h g).coeff 1))
  (w : PowerSeries (IsLocalRing.ResidueField O)) (hw : w.constantCoeff = 0)
  (hwlinear : IsUnit (w.coeff 1))
  (heq : ∀ g, PowerSeries.subst (f g) w = PowerSeries.subst w (h g))

include hw hwlinear heq

/-- A genuine common coordinate intertwining every group element preserves
the whole completed lifting condition. -/
theorem liftable_iff_of_intertwining :
    Liftable π hπ h hhzero hhlinear ↔ Liftable π hπ f hfzero hflinear := by
  have hfamily : h = fun g ↦ powerSeriesConjugate (f g) w hwlinear := by
    funext g
    exact (powerSeriesConjugate_eq_of_intertwining (f g) (h g) w hw hwlinear (heq g)).symm
  subst h
  exact liftable_coordinateChange_iff π hπ f hfzero hflinear w hw hwlinear

/-- The same actual intertwining preserves full-family liftability at every
fixed positive coefficient level. -/
theorem finiteLiftable_iff_of_intertwining (r : ℕ) (hr : 1 ≤ r) :
    FiniteLiftable π hπ h hhzero hhlinear r hr ↔ FiniteLiftable π hπ f hfzero hflinear r hr := by
  have hfamily : h = fun g ↦ powerSeriesConjugate (f g) w hwlinear := by
    funext g
    exact (powerSeriesConjugate_eq_of_intertwining (f g) (h g) w hw hwlinear (heq g)).symm
  subst h
  exact finiteLiftable_coordinateChange_iff π hπ f hfzero hflinear r hr w hw hwlinear

end Intertwining

section OriginalNormCoordinates

open FontaineWintenberger WithZero
open scoped LaurentSeries

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
  [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
  (p : ℕ) [Fact p.Prime]
  [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p]
  (hAPF : IsAPF K L) (hInf : ¬ Module.Finite K L)

local notation "κL" => IsLocalRing.ResidueField
  (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L)
local notation "κK" => IsLocalRing.ResidueField
  (Valuation.valuationSubring (NormedField.valuation (K := K)))

/-- Any two actual original normalized uniformizers are related by a
genuine residue power-series coordinate. Its evaluation identity holds on
every power series, in the original norm field. -/
theorem exists_normLimitUniformizer_coordinateChange (u v : NormLimit K L)
    (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ))
    (hv : normLimitValuation K L hAPF v = exp (-1 : ℤ)) :
    letI := normLimitField K L p hAPF hInf
    ∃ w : PowerSeries κL, w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) ∧
      normLimitLaurentEquiv K L p hAPF hInf u hu (w : LaurentSeries κL) = v ∧
        ∀ A : PowerSeries κL,
          normLimitLaurentEquiv K L p hAPF hInf v hv (A : LaurentSeries κL) =
            normLimitLaurentEquiv K L p hAPF hInf u hu (A.subst w : LaurentSeries κL) := by
  let := normLimitField K L p hAPF hInf
  let := normLimitValued K L p hAPF hInf
  let eu := normLimitLaurentEquiv K L p hAPF hInf u hu
  let ev := normLimitLaurentEquiv K L p hAPF hInf v hv
  let F := ev.trans eu.symm
  have hFval (A : LaurentSeries κL) :
      (Valued.v (F A) : WithZero (Multiplicative ℤ)) = Valued.v A := by
    calc
      _ = normLimitValuation K L hAPF (eu (F A)) :=
        (normLimitLaurentEquiv_valuation K L p hAPF hInf u hu (F A)).symm
      _ = normLimitValuation K L hAPF (ev A) := by
        change normLimitValuation K L hAPF (eu (eu.symm (ev A))) = _
        rw [eu.apply_symm_apply]
      _ = Valued.v A := normLimitLaurentEquiv_valuation K L p hAPF hInf v hv A
  have hFC (a : κL) : F (HahnSeries.C a) = HahnSeries.C a := by
    apply eu.injective
    change eu (eu.symm (ev (HahnSeries.C a))) = eu (HahnSeries.C a)
    rw [eu.apply_symm_apply]
    simpa only [LaurentSeries.algebraMap_apply] using
      (normLimitLaurentEquiv_C K L p hAPF hInf v hv a).trans
        (normLimitLaurentEquiv_C K L p hAPF hInf u hu a).symm
  obtain ⟨w, hw, hzero, hlinear, hsubst⟩ := exists_coordinateChange_of_valuedEquiv F hFval hFC
  refine ⟨w, hzero, hlinear, ?_, ?_⟩
  · rw [hw]
    change eu (eu.symm (ev (HahnSeries.single (1 : ℤ) 1))) = v
    rw [eu.apply_symm_apply]
    simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
      normLimitLaurentEquiv_X K L p hAPF hInf v hv
  · intro A
    have h := congrArg eu (hsubst A)
    change eu (eu.symm (ev (A : LaurentSeries κL))) = eu (A.subst w : LaurentSeries κL) at h
    simpa only [eu.apply_symm_apply] using h

/-- One actual coordinate change simultaneously intertwines every original
Galois coordinate. Coefficient fixing and ordinary substitution are the
proved consequences of actual residue triviality. -/
theorem exists_sourceNormFieldCoordinate_coordinateChange [IsGalois K L]
    (hres : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) κL))
    (u v : NormLimit K L)
    (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ))
    (hv : normLimitValuation K L hAPF v = exp (-1 : ℤ)) :
    ∃ w : PowerSeries κL, w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) ∧
      ∀ g : L ≃ₐ[K] L,
        PowerSeries.subst (sourceNormFieldCoordinate K L p hAPF hInf u hu g) w =
          PowerSeries.subst w (sourceNormFieldCoordinate K L p hAPF hInf v hv g) := by
  let := normLimitField K L p hAPF hInf
  let eu := normLimitLaurentEquiv K L p hAPF hInf u hu
  let ev := normLimitLaurentEquiv K L p hAPF hInf v hv
  obtain ⟨w, hzero, hlinear, hevalw, hchange⟩ :=
    exists_normLimitUniformizer_coordinateChange K L p hAPF hInf u v hu hv
  refine ⟨w, hzero, hlinear, ?_⟩
  intro g
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  apply eu.injective
  have haction := congrArg eu
    (sourceNormFieldLaurentAction_powerSeries K L p hAPF hInf hres u hu g w)
  change eu (eu.symm (normLimitAut K p hAPF hInf g (eu (w : LaurentSeries κL)))) =
    eu (w.subst (sourceNormFieldCoordinate K L p hAPF hInf u hu g) : LaurentSeries κL) at haction
  have haction' :
      eu (w.subst (sourceNormFieldCoordinate K L p hAPF hInf u hu g) : LaurentSeries κL) =
        normLimitAut K p hAPF hInf g (eu (w : LaurentSeries κL)) := by
    simpa only [eu.apply_symm_apply] using haction.symm
  calc
    _ = normLimitAut K p hAPF hInf g (eu (w : LaurentSeries κL)) := haction'
    _ = normLimitAut K p hAPF hInf g v := congrArg (normLimitAut K p hAPF hInf g) hevalw
    _ = ev (sourceNormFieldCoordinate K L p hAPF hInf v hv g : LaurentSeries κL) :=
      (sourceNormFieldCoordinate_eval K L p hAPF hInf v hv g).symm
    _ = _ := hchange (sourceNormFieldCoordinate K L p hAPF hInf v hv g)

/-- Transporting through the same two actual residue identifications gives
one common coordinate change for the entire coefficient-residue family.
The specified residue identification is preserved, rather than replaced. -/
theorem exists_bergerCoordinateFamily_coordinateChange [IsGalois K L]
    (hres : Function.Surjective (algebraMap κK κL))
    (E : Type*) [Field E] [Algebra (Padic p) E] [FiniteDimensional (Padic p) E]
    (ε : IsLocalRing.ResidueField (spectralIntegerRing (Padic p) E) ≃+* κK)
    (u v : NormLimit K L)
    (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ))
    (hv : normLimitValuation K L hAPF v = exp (-1 : ℤ)) :
    ∃ w : PowerSeries (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) E)),
      w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) ∧
        ∀ g : L ≃ₐ[K] L,
          PowerSeries.subst (bergerCoordinateFamily K L p hAPF hInf hres u hu E ε g) w =
            PowerSeries.subst w (bergerCoordinateFamily K L p hAPF hInf hres v hv E ε g) := by
  obtain ⟨w, hzero, hlinear, hcomm⟩ :=
    exists_sourceNormFieldCoordinate_coordinateChange K L p hAPF hInf hres u v hu hv
  let ψ := (normFieldBaseResidueEquiv K L hres).symm.toRingHom
  have hzeroK : (w.map ψ).constantCoeff = 0 := by
    change ψ w.constantCoeff = 0
    rw [hzero, map_zero]
  have hzeroE : ((w.map ψ).map ε.symm.toRingHom).constantCoeff = 0 := by
    change ε.symm.toRingHom ((w.map ψ).constantCoeff) = 0
    rw [hzeroK, map_zero]
  have hlinearE : IsUnit (((w.map ψ).map ε.symm.toRingHom).coeff 1) := by
    simpa only [PowerSeries.coeff_map] using (hlinear.map ψ).map ε.symm.toRingHom
  refine ⟨(w.map ψ).map ε.symm.toRingHom, hzeroE, hlinearE, ?_⟩
  intro g
  have hbase :
      PowerSeries.subst (normFieldCoordinate K L p hAPF hInf hres u hu g) (w.map ψ) =
        PowerSeries.subst (w.map ψ) (normFieldCoordinate K L p hAPF hInf hres v hv g) := by
    calc
      _ = (PowerSeries.subst (sourceNormFieldCoordinate K L p hAPF hInf u hu g) w).map ψ :=
        (PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
          (sourceNormFieldCoordinate_constantCoeff K L p hAPF hInf u hu g)) w).symm
      _ = (PowerSeries.subst w (sourceNormFieldCoordinate K L p hAPF hInf v hv g)).map ψ :=
        congrArg (PowerSeries.map ψ) (hcomm g)
      _ = _ := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hzero) _
  calc
    _ = (PowerSeries.subst (normFieldCoordinate K L p hAPF hInf hres u hu g) (w.map ψ)).map
        ε.symm.toRingHom :=
      (PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
        (normFieldCoordinate_constantCoeff K L p hAPF hInf hres u hu g)) _).symm
    _ = (PowerSeries.subst (w.map ψ) (normFieldCoordinate K L p hAPF hInf hres v hv g)).map
        ε.symm.toRingHom := congrArg (PowerSeries.map ε.symm.toRingHom) hbase
    _ = _ := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hzeroK) _

/-- For the same actual residue identification and coefficient uniformizer,
complete liftability is independent of the original norm-field uniformizer. -/
theorem bergerCoordinateFamily_liftable_iff [IsGalois K L]
    (hres : Function.Surjective (algebraMap κK κL))
    (E : Type*) [Field E] [Algebra (Padic p) E] [FiniteDimensional (Padic p) E]
    (ε : IsLocalRing.ResidueField (spectralIntegerRing (Padic p) E) ≃+* κK)
    (ϖ : spectralIntegerRing (Padic p) E) (hϖ : Irreducible ϖ)
    (u v : NormLimit K L)
    (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ))
    (hv : normLimitValuation K L hAPF v = exp (-1 : ℤ)) :
    let := bergerCoefficientResidue_finite p E
    Liftable ϖ hϖ
        (bergerCoordinateFamily K L p hAPF hInf hres v hv E ε)
        (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres v hv E ε)
        (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres v hv E ε) ↔
      Liftable ϖ hϖ
        (bergerCoordinateFamily K L p hAPF hInf hres u hu E ε)
        (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres u hu E ε)
        (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres u hu E ε) := by
  let := bergerCoefficientResidue_finite p E
  obtain ⟨w, hzero, hlinear, hcomm⟩ :=
    exists_bergerCoordinateFamily_coordinateChange K L p hAPF hInf hres E ε u v hu hv
  exact liftable_iff_of_intertwining ϖ hϖ _ _ _ _ _ _ w hzero hlinear hcomm

/-- The same two original uniformizers give equivalent full-family lifting
conditions in each original positive coefficient quotient. -/
theorem bergerCoordinateFamily_finiteLiftable_iff [IsGalois K L]
    (hres : Function.Surjective (algebraMap κK κL))
    (E : Type*) [Field E] [Algebra (Padic p) E] [FiniteDimensional (Padic p) E]
    (ε : IsLocalRing.ResidueField (spectralIntegerRing (Padic p) E) ≃+* κK)
    (ϖ : spectralIntegerRing (Padic p) E) (hϖ : Irreducible ϖ)
    (u v : NormLimit K L)
    (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ))
    (hv : normLimitValuation K L hAPF v = exp (-1 : ℤ)) (r : ℕ) (hr : 1 ≤ r) :
    let := bergerCoefficientResidue_finite p E
    FiniteLiftable ϖ hϖ
        (bergerCoordinateFamily K L p hAPF hInf hres v hv E ε)
        (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres v hv E ε)
        (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres v hv E ε) r hr ↔
      FiniteLiftable ϖ hϖ
        (bergerCoordinateFamily K L p hAPF hInf hres u hu E ε)
        (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres u hu E ε)
        (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres u hu E ε) r hr := by
  let := bergerCoefficientResidue_finite p E
  obtain ⟨w, hzero, hlinear, hcomm⟩ :=
    exists_bergerCoordinateFamily_coordinateChange K L p hAPF hInf hres E ε u v hu hv
  exact finiteLiftable_iff_of_intertwining ϖ hϖ _ _ _ _ _ _ w hzero hlinear hcomm r hr

end OriginalNormCoordinates

end FalseTateNonliftability.CoefficientRing

namespace FalseTateNonliftability

open FontaineWintenberger WithZero

section IntrinsicUniformizer

variable {p : ℕ} [Fact p.Prime]
  (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
  [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
  [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p]
  (L : Type*) [Field L] [Algebra K L] [IsGalois K L]
  [Fact (IsAPF K L)] [Fact (¬ Module.Finite K L)]
  [Fact (Function.Surjective
    (algebraMap (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
      (IsLocalRing.ResidueField
        (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L))))]
  (E : Type*) [Field E] [Algebra (Padic p) E] [FiniteDimensional (Padic p) E]

local notation "κK" => IsLocalRing.ResidueField
  (Valuation.valuationSubring (NormedField.valuation (K := K)))
local notation "κL" => IsLocalRing.ResidueField
  (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L)
local notation "O_E" => spectralIntegerRing (Padic p) E
local notation "κE" => IsLocalRing.ResidueField O_E
local notation "hAPF" => (Fact.out : IsAPF K L)
local notation "hInf" => (Fact.out : ¬ Module.Finite K L)
local notation "hres" => (Fact.out : Function.Surjective (algebraMap κK κL))

/-- Berger's intrinsic property can be tested in any specified actual
normalized uniformizer. The same residue identification and coefficient
uniformizer witnesses transport from its internally fixed uniformizer. -/
theorem bergerLiftable_iff_uniformizer (u : NormLimit K L)
    (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ)) :
    letI := bergerCoefficientResidue_finite p E
    BergerLiftable K L E ↔
      ∃ (ε : κE ≃+* κK) (ϖ : O_E) (hϖ : Irreducible ϖ),
        CoefficientRing.Liftable ϖ hϖ
          (bergerCoordinateFamily K L p hAPF hInf hres u hu E ε)
          (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres u hu E ε)
          (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres u hu E ε) := by
  let := bergerCoefficientResidue_finite p E
  constructor
  · rintro ⟨ε, ϖ, hϖ, hLift⟩
    refine ⟨ε, ϖ, hϖ, ?_⟩
    exact (CoefficientRing.bergerCoordinateFamily_liftable_iff K L p hAPF hInf hres E ε ϖ hϖ
      (normLimitUniformizer K L p hAPF hInf) u
      (normLimitValuation_normLimitUniformizer K L p hAPF hInf) hu).mpr hLift
  · rintro ⟨ε, ϖ, hϖ, hLift⟩
    refine ⟨ε, ϖ, hϖ, ?_⟩
    exact (CoefficientRing.bergerCoordinateFamily_liftable_iff K L p hAPF hInf hres E ε ϖ hϖ
      (normLimitUniformizer K L p hAPF hInf) u
      (normLimitValuation_normLimitUniformizer K L p hAPF hInf) hu).mp hLift

/-- Existence of lifts in some actual normalized norm-field coordinate is
equivalent to the intrinsic property defined with the fixed coordinate. -/
theorem bergerLiftable_iff_exists_uniformizer :
    letI := bergerCoefficientResidue_finite p E
    BergerLiftable K L E ↔
      ∃ (u : NormLimit K L) (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ))
        (ε : κE ≃+* κK) (ϖ : O_E) (hϖ : Irreducible ϖ),
        CoefficientRing.Liftable ϖ hϖ
          (bergerCoordinateFamily K L p hAPF hInf hres u hu E ε)
          (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres u hu E ε)
          (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres u hu E ε) := by
  let := bergerCoefficientResidue_finite p E
  constructor
  · intro hB
    refine ⟨normLimitUniformizer K L p hAPF hInf,
      normLimitValuation_normLimitUniformizer K L p hAPF hInf, ?_⟩
    exact (bergerLiftable_iff_uniformizer K L E _ _).mp hB
  · rintro ⟨u, hu, hLift⟩
    exact (bergerLiftable_iff_uniformizer K L E u hu).mpr hLift

/-- Equivalently, every actual normalized norm-field uniformizer admits
the full lifting data. Uniformizer existence is supplied by the original
norm-limit construction, so this quantifier is nonvacuous. -/
theorem bergerLiftable_iff_forall_uniformizer :
    letI := bergerCoefficientResidue_finite p E
    BergerLiftable K L E ↔
      ∀ (u : NormLimit K L) (hu : normLimitValuation K L hAPF u = exp (-1 : ℤ)),
        ∃ (ε : κE ≃+* κK) (ϖ : O_E) (hϖ : Irreducible ϖ),
          CoefficientRing.Liftable ϖ hϖ
            (bergerCoordinateFamily K L p hAPF hInf hres u hu E ε)
            (bergerCoordinateFamily_constantCoeff K L p hAPF hInf hres u hu E ε)
            (bergerCoordinateFamily_linear_isUnit K L p hAPF hInf hres u hu E ε) := by
  let := bergerCoefficientResidue_finite p E
  constructor
  · intro hB u hu
    exact (bergerLiftable_iff_uniformizer K L E u hu).mp hB
  · intro hAll
    exact (bergerLiftable_iff_uniformizer K L E
      (normLimitUniformizer K L p hAPF hInf)
      (normLimitValuation_normLimitUniformizer K L p hAPF hInf)).mpr
        (hAll _ (normLimitValuation_normLimitUniformizer K L p hAPF hInf))

end IntrinsicUniformizer

end FalseTateNonliftability
