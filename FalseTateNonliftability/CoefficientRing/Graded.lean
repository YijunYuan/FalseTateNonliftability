module

public import FalseTateNonliftability.CoefficientRing.Truncation
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual graded layers of truncated Laurent coefficient rings

The layer is the quotient of the original principal ideals, restricted to
the actual scalar action of `O`. Multiplication by the uniformizer power
identifies it with Laurent series over the actual residue field, without
choosing an embedding of that field into `O`.

This proves blueprint lemma `nl:truncated-coefficient-graded-layer`.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

variable {O : Type*} [CommRing O]

local instance laurentScalarTower {S : Type*} [CommRing S] [Algebra O S] :
    IsScalarTower O (LaurentSeries S) (LaurentSeries S) where
  smul_assoc b f g := by
    change (b • f) * g = b • (f * g)
    have h (x : LaurentSeries S) : b • x = HahnSeries.C (algebraMap O S b) * x := by
      rw [HahnSeries.C_mul_eq_smul]
      ext n
      simp only [HahnSeries.coeff_smul, Algebra.smul_def]
      rfl
    rw [h f, h (f * g), mul_assoc]

local instance laurentSMulCommClass {S : Type*} [CommRing S] [Algebra O S] :
    SMulCommClass O (LaurentSeries S) (LaurentSeries S) where
  smul_comm b f g := by
    change b • (f * g) = f * (b • g)
    have h : (b • g) * f = b • (g * f) := smul_assoc b g f
    rw [mul_comm f g, ← h, mul_comm]

/-- The original principal ideal in the actual truncated Laurent ring. -/
def layerIdeal (π : O) (r j : ℕ) : Ideal (LaurentSeries (Truncation π r)) :=
  Ideal.span {(HahnSeries.C (parameter π r)) ^ j}

/-- The original ideal with the original coefficient scalar action. -/
def layerSubmodule (π : O) (r j : ℕ) : Submodule O (LaurentSeries (Truncation π r)) :=
  (layerIdeal π r j).restrictScalars O

/-- The next original ideal inside the current one, through the actual inclusion. -/
def nextLayerSubmodule (π : O) (r j : ℕ) : Submodule O (layerSubmodule π r j) :=
  Submodule.comap (layerSubmodule π r j).subtype (layerSubmodule π r (j + 1))

/-- The actual submodule quotient, introducing no replacement Laurent carrier. -/
abbrev GradedLayer (π : O) (r j : ℕ) :=
  @HasQuotient.Quotient (layerSubmodule π r j) _
    (Submodule.hasQuotient (R := O) (M := layerSubmodule π r j)) (nextLayerSubmodule π r j)

/-- Original Laurent reduction, as a linear map for the original coefficient action. -/
def reductionLinear (π : O) (r : ℕ) : LaurentSeries O →ₗ[O] LaurentSeries (Truncation π r) where
  __ := (principalReduction (π ^ r)).toAddMonoidHom
  map_smul' b f := by
    ext n
    simp only [HahnSeries.coeff_smul, Algebra.smul_def]
    rfl

/-- Principal ideals map to the corresponding original truncated ideals. -/
theorem map_span_C_pow (π : O) (r j : ℕ) :
    (Ideal.span {((HahnSeries.C π : LaurentSeries O) ^ j)}).map
      (principalReduction (π ^ r)) = layerIdeal π r j := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]
  change Ideal.span {(mapRingHom (Ideal.Quotient.mk _) (HahnSeries.C π)) ^ j} = _
  rw [mapRingHom_C]
  rfl

/-- Pulling a layer ideal back through actual reduction gives its original ideal. -/
theorem reduction_mem_layerIdeal_iff (π : O) (r j : ℕ) (hjr : j ≤ r) (f : LaurentSeries O) :
    principalReduction (π ^ r) f ∈ layerIdeal π r j ↔
      f ∈ Ideal.span {((HahnSeries.C π : LaurentSeries O) ^ j)} := by
  rw [← map_span_C_pow π r j]
  change f ∈ (Ideal.map (principalReduction (π ^ r))
    (Ideal.span {((HahnSeries.C π : LaurentSeries O) ^ j)})).comap
      (principalReduction (π ^ r)) ↔ _
  rw [Ideal.comap_map_of_surjective _ (principalReduction_surjective (π ^ r)),
    ← RingHom.ker_eq_comap_bot, ker_principalReduction]
  have hker : Ideal.span {(HahnSeries.C (π ^ r) : LaurentSeries O)} ≤
      Ideal.span {((HahnSeries.C π : LaurentSeries O) ^ j)} := by
    rw [map_pow (HahnSeries.C : O →+* LaurentSeries O) π r]
    exact span_pow_le (HahnSeries.C π : LaurentSeries O) hjr
  rw [sup_eq_left.mpr hker]

/-- Multiplication and passage to the actual ideal quotient, on original Laurent lifts. -/
def gradedLift (π : O) (r j : ℕ) : LaurentSeries O →ₗ[O] GradedLayer π r j where
  toFun f := Submodule.Quotient.mk
    (⟨(HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) f,
      Ideal.mem_span_singleton.mpr ⟨_, rfl⟩⟩ : layerSubmodule π r j)
  map_add' f g := by
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change (HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) (f + g) =
      (HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) f +
        (HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) g
    rw [map_add, mul_add]
  map_smul' b f := by
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    change (HahnSeries.C (parameter π r)) ^ j * reductionLinear π r (b • f) =
      b • ((HahnSeries.C (parameter π r)) ^ j * reductionLinear π r f)
    rw [map_smul, mul_smul_comm]

@[simp]
theorem gradedLift_apply (π : O) (r j : ℕ) (f : LaurentSeries O) :
    gradedLift π r j f = Submodule.Quotient.mk
      (⟨(HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) f,
        Ideal.mem_span_singleton.mpr ⟨_, rfl⟩⟩ : layerSubmodule π r j) := rfl

/-- Every element of the actual layer has an original Laurent representative. -/
theorem gradedLift_surjective (π : O) (r j : ℕ) : Function.Surjective (gradedLift π r j) := by
  intro x
  obtain ⟨⟨a, ha⟩, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  obtain ⟨f, hf⟩ := principalReduction_surjective (π ^ r) b
  refine ⟨f, ?_⟩
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact (congrArg (fun b ↦ (HahnSeries.C (parameter π r)) ^ j * b) hf).trans hb.symm

/-- The actual residue-coefficient map, linear for the original `O` action. -/
def residueLinear [IsLocalRing O] : LaurentSeries O →ₗ[O] LaurentSeries (IsLocalRing.ResidueField O) where
  __ := (mapRingHom (IsLocalRing.residue O)).toAddMonoidHom
  map_smul' b f := by
    ext n
    simp only [HahnSeries.coeff_smul, Algebra.smul_def]
    rfl

/-- Every Laurent series over the actual residue field has an original Laurent lift. -/
theorem residueLinear_surjective [IsLocalRing O] : Function.Surjective (residueLinear (O := O)) :=
  mapRingHom_surjective _ Ideal.Quotient.mk_surjective

section Domain

variable [IsDomain O] (π : O) (hπ : π ≠ 0)

include hπ in
/-- Cancellation takes place in the original Laurent domain, and the actual
layer map has exactly the original principal kernel. -/
theorem ker_gradedLift (r j : ℕ) (hjr : j < r) :
    LinearMap.ker (gradedLift π r j) =
      (Ideal.span {(HahnSeries.C π : LaurentSeries O)}).restrictScalars O := by
  ext f
  change gradedLift π r j f = 0 ↔ f ∈ Ideal.span {(HahnSeries.C π : LaurentSeries O)}
  rw [gradedLift_apply, Submodule.Quotient.mk_eq_zero]
  change (HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) f ∈
    layerIdeal π r (j + 1) ↔ _
  have heq : (HahnSeries.C (parameter π r)) ^ j * principalReduction (π ^ r) f =
      principalReduction (π ^ r) ((HahnSeries.C π) ^ j * f) := by
    rw [map_mul, map_pow]
    simp only [principalReduction, mapRingHom_C]
    rfl
  rw [heq, reduction_mem_layerIdeal_iff π r (j + 1) (by omega),
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ]
  exact mul_dvd_mul_iff_left (pow_ne_zero j (HahnSeries.C_ne_zero hπ))

end Domain

section DiscreteValuationRing

variable [IsDomain O] [IsDiscreteValuationRing O] (π : O) (hπ : Irreducible π)

include hπ in
/-- The original actual residue map has exactly the same original principal kernel. -/
theorem ker_residueLinear : LinearMap.ker (residueLinear (O := O)) =
    (Ideal.span {(HahnSeries.C π : LaurentSeries O)}).restrictScalars O := by
  ext f
  change mapRingHom (IsLocalRing.residue O) f = 0 ↔
    f ∈ Ideal.span {(HahnSeries.C π : LaurentSeries O)}
  rw [HahnSeries.ext_iff, funext_iff, mem_span_C_iff]
  simp only [mapRingHom_coeff, HahnSeries.coeff_zero]
  change (∀ n, Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (f.coeff n) = 0) ↔ _
  simp only [Ideal.Quotient.eq_zero_iff_mem, hπ.maximalIdeal_eq]

/-- The actual first-isomorphism-theorem identification of the original residue
Laurent series with the original ideal quotient. -/
def gradedLayerEquiv (r j : ℕ) (hjr : j < r) :
    LaurentSeries (IsLocalRing.ResidueField O) ≃ₗ[O] GradedLayer π r j :=
  ((residueLinear (O := O)).quotKerEquivOfSurjective residueLinear_surjective).symm.trans
    ((Submodule.quotEquivOfEq _ _
      ((ker_residueLinear π hπ).trans (ker_gradedLift π hπ.ne_zero r j hjr).symm)).trans
        ((gradedLift π r j).quotKerEquivOfSurjective (gradedLift_surjective π r j)))

/-- Multiplication of an original lift is the exact computation of the layer identification. -/
@[simp]
theorem gradedLayerEquiv_apply (r j : ℕ) (hjr : j < r) (f : LaurentSeries O) :
    gradedLayerEquiv π hπ r j hjr (residueLinear f) = gradedLift π r j f := by
  simp only [gradedLayerEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The inverse identification computes the actual residue of the original lift. -/
@[simp]
theorem gradedLayerEquiv_symm_apply (r j : ℕ) (hjr : j < r) (f : LaurentSeries O) :
    (gradedLayerEquiv π hπ r j hjr).symm (gradedLift π r j f) = residueLinear f := by
  rw [← gradedLayerEquiv_apply π hπ r j hjr f, LinearEquiv.symm_apply_apply]

include hπ in
/-- Equality of actual layer classes is equivalent to equality of actual residues;
in particular the multiplication formula is independent of every chosen lift. -/
theorem gradedLift_eq_iff (r j : ℕ) (hjr : j < r) (f g : LaurentSeries O) :
    gradedLift π r j f = gradedLift π r j g ↔ residueLinear f = residueLinear g := by
  constructor
  · intro h
    apply (gradedLayerEquiv π hπ r j hjr).injective
    simpa only [gradedLayerEquiv_apply] using h
  · intro h
    exact (gradedLayerEquiv_apply π hπ r j hjr f).symm.trans
      ((congrArg (gradedLayerEquiv π hπ r j hjr) h).trans (gradedLayerEquiv_apply π hπ r j hjr g))

/-- Actual coefficient reduction followed by actual residue is original residue. -/
theorem map_residue_principalReduction (r : ℕ) (hr : 1 ≤ r) (f : LaurentSeries O) :
    mapRingHom (residue π hπ r hr) (principalReduction (π ^ r) f) = residueLinear f := by
  ext n
  exact residue_mk π hπ r hr (f.coeff n)

/-- The layer formula on an arbitrary truncated Laurent representative. -/
theorem gradedLayerEquiv_apply_residue (r j : ℕ) (hjr : j < r)
    (g : LaurentSeries (Truncation π r)) :
    gradedLayerEquiv π hπ r j hjr (mapRingHom (residue π hπ r (by omega)) g) =
      Submodule.Quotient.mk
        (⟨(HahnSeries.C (parameter π r)) ^ j * g,
          Ideal.mem_span_singleton.mpr ⟨_, rfl⟩⟩ : layerSubmodule π r j) := by
  obtain ⟨f, rfl⟩ := principalReduction_surjective (π ^ r) g
  rw [map_residue_principalReduction, gradedLayerEquiv_apply]
  rfl

end DiscreteValuationRing

section CoefficientExtension

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
  [Algebra (Padic p) F] [FiniteDimensional (Padic p) F]

local notation "O_F" => FontaineWintenberger.spectralIntegerRing (Padic p) F

/-- The actual graded-layer equivalence for a finite coefficient extension,
using its actual spectral integers, residue map, and uniformizer. -/
abbrev coefficientExtensionGradedLayerEquiv (π : O_F) (hπ : Irreducible π)
    (r j : ℕ) (hjr : j < r) :
    LaurentSeries (IsLocalRing.ResidueField O_F) ≃ₗ[O_F] GradedLayer π r j :=
  gradedLayerEquiv π hπ r j hjr

/-- Its original-lift computation uses the same actual residue map. -/
theorem coefficientExtensionGradedLayerEquiv_apply (π : O_F) (hπ : Irreducible π)
    (r j : ℕ) (hjr : j < r) (f : LaurentSeries O_F) :
    coefficientExtensionGradedLayerEquiv p F π hπ r j hjr (residueLinear f) =
      gradedLift π r j f := gradedLayerEquiv_apply π hπ r j hjr f

end CoefficientExtension

end FalseTateNonliftability.CoefficientRing
