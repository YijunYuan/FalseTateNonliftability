/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Liftability
public import FontaineWintenberger.FieldOfNorms.LaurentCoordinates
public import FontaineWintenberger.FieldOfNorms.FaithfulAction
public import FontaineWintenberger.LocalField.LaurentSubstitution

/-!
# Berger liftability of an actual field extension

The normalized norm-family uniformizer is the existing fixed one. Compatible
residue identifications and coefficient uniformizers are quantified internally.
-/

@[expose] public section

noncomputable section

open Filter FontaineWintenberger WithZero LaurentSeries
open scoped Topology

namespace FalseTateNonliftability

namespace CoefficientRing

variable {k : Type*} [Field k]

/-- A literal Laurent element of normalized uniformizer valuation is an
ordinary invertible power-series coordinate. -/
theorem exists_powerSeries_coordinate_of_valuation (a : LaurentSeries k)
    (ha : (Valued.v a : WithZero (Multiplicative ℤ)) = exp (-1 : ℤ)) :
    ∃ w : PowerSeries k, (w : LaurentSeries k) = a ∧
      w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) := by
  have hle : exp (-1 : ℤ) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  obtain ⟨w, hw⟩ := (LaurentSeries.val_le_one_iff_eq_coe k a).mp (ha.le.trans hle)
  have hvw : (Valued.v (w : LaurentSeries k) : WithZero (Multiplicative ℤ)) = exp (-1 : ℤ) := by
    rw [hw]
    exact ha
  have hzero : w.constantCoeff = 0 := by
    have hc := LaurentSeries.coeff_zero_of_lt_valuation k hvw.le (show (0 : ℤ) < 1 by omega)
    simpa [PowerSeries.coeff_coe] using hc
  have hlinear : w.coeff 1 ≠ 0 := by
    intro hlinear
    have hcoeff (n : ℤ) (hn : n < 2) : (w : LaurentSeries k).coeff n = 0 := by
      by_cases hn0 : n < 0
      · rw [PowerSeries.coeff_coe]
        simp only [hn0, ite_true]
      · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
        · simpa [PowerSeries.coeff_coe] using hzero
        · simpa [PowerSeries.coeff_coe] using hlinear
    have hbound : (Valued.v (w : LaurentSeries k) : WithZero (Multiplicative ℤ)) ≤ exp (-2 : ℤ) :=
      (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mpr hcoeff
    rw [hvw] at hbound
    exact not_le_of_gt (WithZero.exp_lt_exp.mpr (by omega : (-2 : ℤ) < -1)) hbound
  exact ⟨w, hw, hzero, isUnit_iff_ne_zero.mpr hlinear⟩

end CoefficientRing

section ActualCoordinates

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
  [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L]
variable (p : ℕ) [Fact p.Prime]
  [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)
variable (hres : Function.Surjective
  (algebraMap (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
    (IsLocalRing.ResidueField
      (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L))))

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "κK" => IsLocalRing.ResidueField R
local notation "κL" => IsLocalRing.ResidueField (integralClosure R L)
local notation "K₀" => apfMaximalUnramified K L hL
local notation "K₁" => apfMaximalTame K L hL

/-- The actual residue inclusion is an isomorphism under intrinsic residue triviality. -/
def normFieldBaseResidueEquiv : κK ≃+* κL :=
  RingEquiv.ofBijective (algebraMap κK κL) ⟨(algebraMap κK κL).injective, hres⟩

include hres in
/-- Under actual residue triviality, each source-normalized finite coefficient
coordinate is an element of the original base field. -/
theorem sourceResidueCoordinate_mem_base (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
    ∃ a : K, algebraMap K E.val a = sourceResidueCoordinate K L p hL E hE x := by
  have hs : Function.Surjective
      (algebraMap κK (IsLocalRing.ResidueField (spectralIntegerRing K (K₀).val))) := by
    intro b
    obtain ⟨a, ha⟩ := hres (apfMaximalUnramifiedResidueEquiv K L hL b)
    refine ⟨a, ?_⟩
    apply (apfMaximalUnramifiedResidueEquiv K L hL).injective
    simpa only [AlgEquiv.commutes] using ha
  obtain ⟨a, ha⟩ := hs (sourceResidueRoot K L p hL E hE x)
  have ht := residueTeichmuller_naturality R p (spectralIntegerRing K (K₀).val)
    (algebraMap R (spectralIntegerRing K (K₀).val)) a
  have ht' : algebraMap R (spectralIntegerRing K (K₀).val) (residueTeichmuller R p a) =
      spectralTeichmuller K (K₀).val p (sourceResidueRoot K L p hL E hE x) := by
    change _ = residueTeichmuller (spectralIntegerRing K (K₀).val) p _
    rw [ht]
    congr 1
  refine ⟨(residueTeichmuller R p a : K), ?_⟩
  change algebraMap K E.val (residueTeichmuller R p a : K) =
    (spectralIntegerInclusion K (IntermediateField.inclusion
      ((apfMaximalUnramified_le_maximalTame K L hL).trans hE))
      (spectralTeichmuller K (K₀).val p (sourceResidueRoot K L p hL E hE x)) : E.val)
  rw [← ht']
  rfl

include hres in
/-- The original reindexed norm-family action fixes the actual source
coefficients. Finite normal upper layers reduce the assertion to fixing `K`. -/
theorem normLimitMap_sourceResidueConstants_fixed (g : L ≃ₐ[K] L) (x : κL) :
    normLimitMap g (sourceResidueConstants K L p hL x) = sourceResidueConstants K L p hL x := by
  apply NormLimit.ext K L
  intro D₀
  let D := FiniteLayer.sup D₀ K₁
  let E : FiniteLayer K L := ⟨IntermediateField.normalClosure K D.val L, inferInstance⟩
  have hDE : D ≤ E := IntermediateField.le_normalClosure D.val
  have hD₀E : D₀ ≤ E := (FiniteLayer.le_sup_left D₀ K₁).trans hDE
  have hK₁E : K₁ ≤ E := (FiniteLayer.le_sup_right D₀ K₁).trans hDE
  have hstable : FiniteLayer.map g.symm.toAlgHom E = E :=
    Subtype.ext (IntermediateField.map_normalClosure_eq D.val g.symm)
  have he : normLimitEval K L E (normLimitMap g (sourceResidueConstants K L p hL x)) =
      normLimitEval K L E (sourceResidueConstants K L p hL x) := by
    apply Subtype.ext
    rw [coe_normLimitEval_normLimitMap, hstable,
      normLimitEval_sourceResidueConstants K L p hL E hK₁E]
    obtain ⟨a, ha⟩ := sourceResidueCoordinate_mem_base K L p hL hres E hK₁E x
    have haL : (sourceResidueCoordinate K L p hL E hK₁E x : L) = algebraMap K L a :=
      (congrArg (fun b : E.val => (b : L)) ha).symm
    rw [haL]
    exact g.commutes a
  rw [← normLimitEval_norm K L D₀ E hD₀E
      (normLimitMap g (sourceResidueConstants K L p hL x)),
    ← normLimitEval_norm K L D₀ E hD₀E (sourceResidueConstants K L p hL x), he]

include hres in
/-- The original field automorphism fixes the same actual source coefficient
embedding in the original norm-field structure. -/
theorem normLimitAut_sourceResidueConstants_fixed (g : L ≃ₐ[K] L) (x : κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitAut K p hL hInfinite g
      (sourceResidueConstantsFieldEmbedding K L p hL hInfinite x) =
      sourceResidueConstantsFieldEmbedding K L p hL hInfinite x := by
  let := normLimitField K L p hL hInfinite
  exact normLimitMap_sourceResidueConstants_fixed K L p hL hres g x

variable (u : NormLimit K L) (hu : normLimitValuation K L hL u = exp (-1 : ℤ))

/-- The actual original action, expressed using the already constructed
Laurent coordinates over the intrinsic source residue field. -/
def sourceNormFieldLaurentAction (g : L ≃ₐ[K] L) : LaurentSeries κL ≃+* LaurentSeries κL := by
  letI := normLimitField K L p hL hInfinite
  let e := normLimitLaurentEquiv K L p hL hInfinite u hu
  exact (e.trans (normLimitAut K p hL hInfinite g)).trans e.symm

/-- The conjugated actual action preserves the original Laurent valuation. -/
theorem sourceNormFieldLaurentAction_valuation (g : L ≃ₐ[K] L) (A : LaurentSeries κL) :
    (Valued.v (sourceNormFieldLaurentAction K L p hL hInfinite u hu g A) :
      WithZero (Multiplicative ℤ)) = Valued.v A := by
  let := normLimitField K L p hL hInfinite
  let e := normLimitLaurentEquiv K L p hL hInfinite u hu
  have he : e (sourceNormFieldLaurentAction K L p hL hInfinite u hu g A) =
      normLimitAut K p hL hInfinite g (e A) := e.apply_symm_apply _
  calc
    _ = normLimitValuation K L hL
        (e (sourceNormFieldLaurentAction K L p hL hInfinite u hu g A)) :=
      (normLimitLaurentEquiv_valuation K L p hL hInfinite u hu _).symm
    _ = normLimitValuation K L hL (normLimitAut K p hL hInfinite g (e A)) := congrArg _ he
    _ = normLimitValuation K L hL (e A) := normLimitAut_valuation K p hL hInfinite g (e A)
    _ = Valued.v A := normLimitLaurentEquiv_valuation K L p hL hInfinite u hu A

/-- Continuity is for the existing Laurent valuation topology. -/
theorem continuous_sourceNormFieldLaurentAction (g : L ≃ₐ[K] L) :
    Continuous (sourceNormFieldLaurentAction K L p hL hInfinite u hu g) :=
  (valuedRingEquiv_uniformContinuous _
    (sourceNormFieldLaurentAction_valuation K L p hL hInfinite u hu g)).continuous

include hres in
/-- Residue triviality gives actual fixing of every original coefficient. -/
theorem sourceNormFieldLaurentAction_C (g : L ≃ₐ[K] L) (a : κL) :
    sourceNormFieldLaurentAction K L p hL hInfinite u hu g (HahnSeries.C a) =
      HahnSeries.C a := by
  let := normLimitField K L p hL hInfinite
  let e := normLimitLaurentEquiv K L p hL hInfinite u hu
  apply e.injective
  change e (e.symm (normLimitAut K p hL hInfinite g (e (HahnSeries.C a)))) = _
  rw [e.apply_symm_apply]
  have he : e (HahnSeries.C a) = sourceResidueConstantsFieldEmbedding K L p hL hInfinite a :=
    by simpa only [LaurentSeries.algebraMap_apply] using
      normLimitLaurentEquiv_C K L p hL hInfinite u hu a
  rw [he]
  exact normLimitAut_sourceResidueConstants_fixed K L p hL hInfinite hres g a

theorem sourceNormFieldCoordinate_exists (g : L ≃ₐ[K] L) :
    ∃ f : PowerSeries κL,
      (f : LaurentSeries κL) = sourceNormFieldLaurentAction K L p hL hInfinite u hu g
        (HahnSeries.single (1 : ℤ) 1) ∧
      f.constantCoeff = 0 ∧ IsUnit (f.coeff 1) := by
  apply CoefficientRing.exists_powerSeries_coordinate_of_valuation
  rw [sourceNormFieldLaurentAction_valuation]
  simpa using LaurentSeries.valuation_X_pow κL 1

/-- The actual image of the parameter, as an ordinary power series over the
intrinsic source residue field. -/
def sourceNormFieldCoordinate (g : L ≃ₐ[K] L) : PowerSeries κL :=
  (sourceNormFieldCoordinate_exists K L p hL hInfinite u hu g).choose

/-- The chosen power series is the literal Laurent parameter image. -/
theorem sourceNormFieldCoordinate_coe (g : L ≃ₐ[K] L) :
    (sourceNormFieldCoordinate K L p hL hInfinite u hu g : LaurentSeries κL) =
      sourceNormFieldLaurentAction K L p hL hInfinite u hu g
        (HahnSeries.single (1 : ℤ) 1) :=
  (sourceNormFieldCoordinate_exists K L p hL hInfinite u hu g).choose_spec.1

/-- Actual normalized valuation forces zero constant coefficient. -/
theorem sourceNormFieldCoordinate_constantCoeff (g : L ≃ₐ[K] L) :
    (sourceNormFieldCoordinate K L p hL hInfinite u hu g).constantCoeff = 0 :=
  (sourceNormFieldCoordinate_exists K L p hL hInfinite u hu g).choose_spec.2.1

/-- Actual normalized valuation forces an invertible linear coefficient. -/
theorem sourceNormFieldCoordinate_linear_isUnit (g : L ≃ₐ[K] L) :
    IsUnit ((sourceNormFieldCoordinate K L p hL hInfinite u hu g).coeff 1) :=
  (sourceNormFieldCoordinate_exists K L p hL hInfinite u hu g).choose_spec.2.2

include hres in
/-- The entire original action on power series is ordinary substitution; the
coefficient fixing used here is derived from the actual extension. -/
theorem sourceNormFieldLaurentAction_powerSeries (g : L ≃ₐ[K] L) (A : PowerSeries κL) :
    sourceNormFieldLaurentAction K L p hL hInfinite u hu g (A : LaurentSeries κL) =
      (A.subst (sourceNormFieldCoordinate K L p hL hInfinite u hu g) : LaurentSeries κL) := by
  exact map_ofPowerSeries_eq_subst
    (sourceNormFieldLaurentAction K L p hL hInfinite u hu g).toRingHom
    (continuous_sourceNormFieldLaurentAction K L p hL hInfinite u hu g)
    (sourceNormFieldLaurentAction_C K L p hL hInfinite hres u hu g)
    (sourceNormFieldCoordinate K L p hL hInfinite u hu g)
    (sourceNormFieldCoordinate_constantCoeff K L p hL hInfinite u hu g)
    (sourceNormFieldCoordinate_coe K L p hL hInfinite u hu g).symm A

/-- Evaluation of the coordinate gives the original field automorphism on the
same norm-family uniformizer. -/
theorem sourceNormFieldCoordinate_eval (g : L ≃ₐ[K] L) :
    letI := normLimitField K L p hL hInfinite
    normLimitLaurentEquiv K L p hL hInfinite u hu
      (sourceNormFieldCoordinate K L p hL hInfinite u hu g : LaurentSeries κL) =
      normLimitAut K p hL hInfinite g u := by
  let := normLimitField K L p hL hInfinite
  rw [sourceNormFieldCoordinate_coe]
  change (normLimitLaurentEquiv K L p hL hInfinite u hu)
    ((normLimitLaurentEquiv K L p hL hInfinite u hu).symm
      (normLimitAut K p hL hInfinite g
        ((normLimitLaurentEquiv K L p hL hInfinite u hu)
          (HahnSeries.single (1 : ℤ) 1)))) = _
  rw [RingEquiv.apply_symm_apply]
  have hX := normLimitLaurentEquiv_X K L p hL hInfinite u hu
  simpa only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X] using
    congrArg (normLimitAut K p hL hInfinite g) hX

/-- The literal identity action has the original parameter as coordinate. -/
@[simp]
theorem sourceNormFieldCoordinate_one :
    sourceNormFieldCoordinate K L p hL hInfinite u hu 1 = PowerSeries.X := by
  let := normLimitField K L p hL hInfinite
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [sourceNormFieldCoordinate_coe]
  simp only [sourceNormFieldLaurentAction, RingEquiv.trans_apply, map_one]
  change (normLimitLaurentEquiv K L p hL hInfinite u hu).symm
    (normLimitLaurentEquiv K L p hL hInfinite u hu (HahnSeries.single (1 : ℤ) 1)) = _
  rw [RingEquiv.symm_apply_apply]
  exact HahnSeries.ofPowerSeries_X.symm

include hres in
/-- The genuine group action yields the reversed substitution law. -/
theorem sourceNormFieldCoordinate_mul (g h : L ≃ₐ[K] L) :
    sourceNormFieldCoordinate K L p hL hInfinite u hu (g * h) =
      (sourceNormFieldCoordinate K L p hL hInfinite u hu h).subst
        (sourceNormFieldCoordinate K L p hL hInfinite u hu g) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [sourceNormFieldCoordinate_coe]
  have hmul (A : LaurentSeries κL) :
      sourceNormFieldLaurentAction K L p hL hInfinite u hu (g * h) A =
        sourceNormFieldLaurentAction K L p hL hInfinite u hu g
          (sourceNormFieldLaurentAction K L p hL hInfinite u hu h A) := by
    let := normLimitField K L p hL hInfinite
    simp only [sourceNormFieldLaurentAction, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, map_mul]
    rfl
  rw [hmul, ← sourceNormFieldCoordinate_coe,
    sourceNormFieldLaurentAction_powerSeries K L p hL hInfinite hres]

include hres in
/-- Actual group powers are literal iterates of the ordinary substitution. -/
theorem sourceNormFieldCoordinate_pow (g : L ≃ₐ[K] L) (n : ℕ) :
    sourceNormFieldCoordinate K L p hL hInfinite u hu (g ^ n) =
      (PowerSeries.subst (sourceNormFieldCoordinate K L p hL hInfinite u hu g) :
        PowerSeries κL → PowerSeries κL)^[n] PowerSeries.X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', sourceNormFieldCoordinate_mul K L p hL hInfinite hres,
      ih, Function.iterate_succ_apply']

/-- The actual source coordinate with coefficients in the original base residue
field, using its intrinsic residue inclusion. -/
def normFieldCoordinate (g : L ≃ₐ[K] L) : PowerSeries κK :=
  (sourceNormFieldCoordinate K L p hL hInfinite u hu g).map
    (normFieldBaseResidueEquiv K L hres).symm.toRingHom

/-- Mapping back gives the exact original source-residue coordinate. -/
theorem map_normFieldCoordinate (g : L ≃ₐ[K] L) :
    (normFieldCoordinate K L p hL hInfinite hres u hu g).map
      (normFieldBaseResidueEquiv K L hres).toRingHom =
      sourceNormFieldCoordinate K L p hL hInfinite u hu g := by
  ext n
  simp only [normFieldCoordinate, PowerSeries.coeff_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

/-- Base-residue transport preserves the zero constant coefficient. -/
@[simp]
theorem normFieldCoordinate_constantCoeff (g : L ≃ₐ[K] L) :
    (normFieldCoordinate K L p hL hInfinite hres u hu g).constantCoeff = 0 := by
  simpa only [normFieldCoordinate, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, map_zero] using
    congrArg (normFieldBaseResidueEquiv K L hres).symm.toRingHom
      (sourceNormFieldCoordinate_constantCoeff K L p hL hInfinite u hu g)

/-- Base-residue transport preserves the invertible linear coefficient. -/
theorem normFieldCoordinate_linear_isUnit (g : L ≃ₐ[K] L) :
    IsUnit ((normFieldCoordinate K L p hL hInfinite hres u hu g).coeff 1) := by
  simpa only [normFieldCoordinate, PowerSeries.coeff_map] using
    (sourceNormFieldCoordinate_linear_isUnit K L p hL hInfinite u hu g).map
      (normFieldBaseResidueEquiv K L hres).symm.toRingHom

/-- The base-residue family retains the actual reversed group law. -/
theorem normFieldCoordinate_mul (g h : L ≃ₐ[K] L) :
    normFieldCoordinate K L p hL hInfinite hres u hu (g * h) =
      (normFieldCoordinate K L p hL hInfinite hres u hu h).subst
        (normFieldCoordinate K L p hL hInfinite hres u hu g) := by
  change (sourceNormFieldCoordinate K L p hL hInfinite u hu (g * h)).map _ = _
  rw [sourceNormFieldCoordinate_mul K L p hL hInfinite hres]
  exact PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
    (sourceNormFieldCoordinate_constantCoeff K L p hL hInfinite u hu g)) _

variable (E : Type*) [Field E] [Algebra (Padic p) E] [FiniteDimensional (Padic p) E]

local notation "O_E" => spectralIntegerRing (Padic p) E
local notation "κE" => IsLocalRing.ResidueField O_E

/-- A finite coefficient extension has an actually finite residue field. No
Galois or residue-identification assumption is needed. -/
theorem bergerCoefficientResidue_finite : Finite κE := by
  have : Module.Finite (Valuation.valuationSubring (NormedField.valuation (K := Padic p))) O_E :=
    spectralIntegerRing_moduleFinite (Padic p) E
  have : Module.Finite
      (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring) κE :=
    inferInstance
  exact Module.finite_of_finite
    (IsLocalRing.ResidueField (NormedField.valuation (K := Padic p)).valuationSubring)

/-- The actual coordinate family over the residue field of the coefficient
extension, for a specified compatible residue identification. -/
def bergerCoordinateFamily (ε : κE ≃+* κK) (g : L ≃ₐ[K] L) : PowerSeries κE :=
  (normFieldCoordinate K L p hL hInfinite hres u hu g).map ε.symm.toRingHom

/-- Transport back to the base residue field gives the actual base family. -/
theorem map_bergerCoordinateFamily (ε : κE ≃+* κK) (g : L ≃ₐ[K] L) :
    (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε g).map ε.toRingHom =
      normFieldCoordinate K L p hL hInfinite hres u hu g := by
  ext n
  simp only [bergerCoordinateFamily, PowerSeries.coeff_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

/-- The actual coefficient family has zero constant coefficient. -/
@[simp]
theorem bergerCoordinateFamily_constantCoeff (ε : κE ≃+* κK) (g : L ≃ₐ[K] L) :
    (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε g).constantCoeff = 0 := by
  simpa only [bergerCoordinateFamily, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, map_zero] using
    congrArg ε.symm.toRingHom
      (normFieldCoordinate_constantCoeff K L p hL hInfinite hres u hu g)

/-- The actual coefficient family has an invertible linear coefficient. -/
theorem bergerCoordinateFamily_linear_isUnit (ε : κE ≃+* κK) (g : L ≃ₐ[K] L) :
    IsUnit ((bergerCoordinateFamily K L p hL hInfinite hres u hu E ε g).coeff 1) := by
  simpa only [bergerCoordinateFamily, PowerSeries.coeff_map] using
    (normFieldCoordinate_linear_isUnit K L p hL hInfinite hres u hu g).map ε.symm.toRingHom

/-- The complete transported family retains the genuine reversed group law. -/
theorem bergerCoordinateFamily_mul (ε : κE ≃+* κK) (g h : L ≃ₐ[K] L) :
    bergerCoordinateFamily K L p hL hInfinite hres u hu E ε (g * h) =
      (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε h).subst
        (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε g) := by
  change (normFieldCoordinate K L p hL hInfinite hres u hu (g * h)).map _ = _
  rw [normFieldCoordinate_mul]
  exact PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero'
    (normFieldCoordinate_constantCoeff K L p hL hInfinite hres u hu g)) _

/-- The coefficient-family evaluation is literally the original action on
its original chosen uniformizer, after the two actual residue inclusions. -/
theorem bergerCoordinateFamily_eval (ε : κE ≃+* κK) (g : L ≃ₐ[K] L) :
    letI := normLimitField K L p hL hInfinite
    normLimitLaurentEquiv K L p hL hInfinite u hu
      (mapRingHom (normFieldBaseResidueEquiv K L hres).toRingHom
        (mapRingHom ε.toRingHom
          (HahnSeries.ofPowerSeries ℤ κE
            (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε g)))) =
      normLimitAut K p hL hInfinite g u := by
  let := normLimitField K L p hL hInfinite
  rw [CoefficientRing.mapRingHom_ofPowerSeries, map_bergerCoordinateFamily,
    CoefficientRing.mapRingHom_ofPowerSeries, map_normFieldCoordinate]
  exact sourceNormFieldCoordinate_eval K L p hL hInfinite u hu g

/-- The complete family sends the identity to the parameter. -/
@[simp]
theorem bergerCoordinateFamily_one (ε : κE ≃+* κK) :
    bergerCoordinateFamily K L p hL hInfinite hres u hu E ε 1 = PowerSeries.X := by
  simp [bergerCoordinateFamily, normFieldCoordinate]

/-- Every group power in the actual coefficient family is the genuine
ordinary substitution iterate. -/
theorem bergerCoordinateFamily_pow (ε : κE ≃+* κK) (g : L ≃ₐ[K] L) (n : ℕ) :
    bergerCoordinateFamily K L p hL hInfinite hres u hu E ε (g ^ n) =
      (PowerSeries.subst (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε g) :
        PowerSeries κE → PowerSeries κE)^[n] PowerSeries.X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', bergerCoordinateFamily_mul, ih, Function.iterate_succ_apply']

end ActualCoordinates

section IntrinsicLiftability

variable {p : ℕ} [Fact p.Prime]
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
  [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
  [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L]
  [Fact (IsAPF K L)] [Fact (¬ Module.Finite K L)]
  [Fact (Function.Surjective
    (algebraMap (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
      (IsLocalRing.ResidueField
        (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L))))]
variable (E : Type*) [Field E] [Algebra (Padic p) E] [FiniteDimensional (Padic p) E]

/-- Berger liftability of the actual extension with coefficient field `E`.

The existing fixed normalized norm-family uniformizer is used internally. The
predicate asserts existence of a compatible residue identification and a
coefficient uniformizer; it does not assert independence of an arbitrary residue
identification. Both the Frobenius lift and the full group family range over the
entire canonical principal completion, with no finite-height restriction. -/
def BergerLiftable : Prop :=
  letI : Finite (IsLocalRing.ResidueField (spectralIntegerRing (Padic p) E)) :=
    bergerCoefficientResidue_finite p E
  let hL : IsAPF K L := Fact.out
  let hInfinite : ¬ Module.Finite K L := Fact.out
  let hres : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
        (IsLocalRing.ResidueField
          (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L))) :=
    Fact.out
  let u := normLimitUniformizer K L p hL hInfinite
  let hu := normLimitValuation_normLimitUniformizer K L p hL hInfinite
  ∃ (ε : IsLocalRing.ResidueField (spectralIntegerRing (Padic p) E) ≃+*
      IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
    (ϖ : spectralIntegerRing (Padic p) E) (hϖ : Irreducible ϖ),
    CoefficientRing.Liftable ϖ hϖ
      (bergerCoordinateFamily K L p hL hInfinite hres u hu E ε)
      (bergerCoordinateFamily_constantCoeff K L p hL hInfinite hres u hu E ε)
      (bergerCoordinateFamily_linear_isUnit K L p hL hInfinite hres u hu E ε)

end IntrinsicLiftability

end FalseTateNonliftability
