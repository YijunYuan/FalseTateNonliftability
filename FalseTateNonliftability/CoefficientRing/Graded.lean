/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Truncation
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The layers of the truncated coefficient rings

Let `O` be a discrete valuation ring with maximal ideal `𝔪` and residue field `κ`, and let
`R_r = (O ⧸ 𝔪 ^ (r + 1))((T))`. The ideals `Λ_j = 𝔪 ^ j R_r` of Laurent series with
coefficients in `𝔪 ^ j` form a decreasing filtration with `Λ_0 = R_r` and `Λ_{r + 1} = 0`, and
every element of `Λ_1` other than zero has a unique first nonzero layer `Λ_s ∖ Λ_{s + 1}`. For
`j ≤ r` and a uniformizer `ϖ` of `O`, multiplication by `ϖ ^ j` induces an isomorphism of
`O`-modules `κ((T)) ≃ Λ_j ⧸ Λ_{j + 1}` (Yuan, §2.2). We fix a uniformizer of `O` and write
`layer j X ∈ κ((T))` for the preimage of `X mod Λ_{j + 1}` under this isomorphism, the series
`ϖ⁻ʲ X` of the paper. It is additive, satisfies `layer j (X Z) = layer j X · Z̄`, where `Z̄` is the
residue of `Z`, it is computed coefficientwise, and it commutes with every algebra endomorphism of
`R_r` that reduces to an endomorphism of `κ((T))`.

## Main definitions

* `Truncation.layerIdeal O r j`: the ideal `Λ_j = 𝔪 ^ j R_r`.
* `Truncation.GradedLayer O r j`: the `O`-module `Λ_j ⧸ Λ_{j + 1}`.
* `Truncation.gradedLayerEquiv O r j hj`: the isomorphism `κ((T)) ≃ₗ[O] Λ_j ⧸ Λ_{j + 1}`.
* `Truncation.layer j X`: the series `ϖ⁻ʲ X ∈ κ((T))` for `X ∈ Λ_j`, and `0` for `X ∉ Λ_j`.

## Main results

* `Truncation.exists_unique_first_layer`: an element `X ≠ 0` of `Λ_1` lies in `Λ_s ∖ Λ_{s + 1}`
  for exactly one `1 ≤ s ≤ r`.
* `Truncation.layer_eq_zero_iff`: for `X ∈ Λ_j`, `layer j X = 0` if and only if `X ∈ Λ_{j + 1}`.
* `Truncation.layer_mul`: `layer j (X Z) = layer j X · Z̄`.
* `Truncation.coeff_layer_eq_zero_iff`, `Truncation.coeff_layer_eq_of_coeff_eq_mul`: the
  coefficients of `layer j X`.
* `Truncation.layer_algHom`: `layer j (E X) = E' (layer j X)` if `E` reduces to `E'`.

## Implementation details

The isomorphism `κ((T)) ≃ Λ_j ⧸ Λ_{j + 1}` depends on the uniformizer: replacing `ϖ` by `u ϖ`
multiplies `layer j` by the residue of `u⁻ʲ`. The uniformizer is fixed once by
`IsDiscreteValuationRing.exists_irreducible` and does not appear in any statement of this file.

## References

* Yuan, §2.2.
-/

noncomputable section

namespace FalseTateNonliftability.Truncation

open LaurentSeries
open IsLocalRing (maximalIdeal ResidueField)

@[expose] public section

variable (O : Type*) [CommRing O] [IsLocalRing O]

/-- The ideal `Λ_j = 𝔪 ^ j R_r` of `R_r = (O ⧸ 𝔪 ^ (r + 1))((T))`. -/
def layerIdeal (r j : ℕ) : Ideal (LaurentSeries (Truncation O r)) :=
  (maximalIdeal (Truncation O r) ^ j).map
    (HahnSeries.C : Truncation O r →+* LaurentSeries (Truncation O r))

/-- A constant with coefficient in `𝔪 ^ j` lies in `Λ_j`. -/
theorem C_mem_layerIdeal {r j : ℕ} {x : Truncation O r}
    (hx : x ∈ maximalIdeal (Truncation O r) ^ j) : HahnSeries.C x ∈ layerIdeal O r j :=
  Ideal.mem_map_of_mem _ hx

theorem layerIdeal_antitone (r : ℕ) {i j : ℕ} (hij : i ≤ j) :
    layerIdeal O r j ≤ layerIdeal O r i :=
  Ideal.map_mono (Ideal.pow_le_pow_right hij)

@[simp]
theorem layerIdeal_zero (r : ℕ) : layerIdeal O r 0 = ⊤ := by
  rw [layerIdeal, pow_zero, Ideal.one_eq_top, Ideal.map_top]

/-- `Λ_j = 0` for `j > r`, since `𝔪 ^ (r + 1) = 0` in `O ⧸ 𝔪 ^ (r + 1)`. -/
theorem layerIdeal_eq_bot {r j : ℕ} (hj : r < j) : layerIdeal O r j = ⊥ := by
  rw [layerIdeal, le_bot_iff.mp ((Ideal.pow_le_pow_right hj).trans
    (maximalIdeal_pow_eq_bot O r).le), Ideal.map_bot]

omit [IsLocalRing O] in
private theorem smul_eq_C_mul {S : Type*} [CommRing S] [Algebra O S] (b : O)
    (X : LaurentSeries S) : b • X = HahnSeries.C (algebraMap O S b) * X := by
  rw [HahnSeries.C_mul_eq_smul, algebraMap_smul]

private theorem algHom_C {r : ℕ}
    (E : LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (a : Truncation O r) : E (HahnSeries.C a) = HahnSeries.C a := by
  simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    HahnSeries.ofPowerSeries_C] using E.commutes a

/-- Every `O ⧸ 𝔪 ^ (r + 1)`-algebra endomorphism of `R_r` preserves `Λ_j`. -/
theorem algHom_mem_layerIdeal {r j : ℕ}
    (E : LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j) :
    E X ∈ layerIdeal O r j := by
  have hE : (E : LaurentSeries (Truncation O r) →+* LaurentSeries (Truncation O r)).comp
      HahnSeries.C = HahnSeries.C := RingHom.ext (algHom_C O E)
  have h := Ideal.mem_map_of_mem
    (E : LaurentSeries (Truncation O r) →+* LaurentSeries (Truncation O r)) hX
  rwa [layerIdeal, Ideal.map_map, hE] at h

/-- Every `O ⧸ 𝔪 ^ (r + 1)`-algebra automorphism of `R_r` preserves `Λ_j` in both directions. -/
theorem algEquiv_mem_layerIdeal_iff {r j : ℕ}
    (E : LaurentSeries (Truncation O r) ≃ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (X : LaurentSeries (Truncation O r)) :
    E X ∈ layerIdeal O r j ↔ X ∈ layerIdeal O r j :=
  ⟨fun h ↦ by simpa using algHom_mem_layerIdeal O E.symm.toAlgHom h,
    fun h ↦ algHom_mem_layerIdeal O E.toAlgHom h⟩

/-- A nonzero element of `Λ_1` lies in `Λ_s ∖ Λ_{s + 1}` for exactly one `1 ≤ s ≤ r`. -/
theorem exists_unique_first_layer {r : ℕ} {X : LaurentSeries (Truncation O r)} (hX : X ≠ 0)
    (hX1 : X ∈ layerIdeal O r 1) :
    ∃! s, 1 ≤ s ∧ s ≤ r ∧ X ∈ layerIdeal O r s ∧ X ∉ layerIdeal O r (s + 1) := by
  obtain ⟨s, hsr, hs, hs1⟩ :
      ∃ s, s ≤ r ∧ X ∈ layerIdeal O r s ∧ X ∉ layerIdeal O r (s + 1) := by
    by_contra! h
    have hmem (n : ℕ) (hn : n ≤ r + 1) : X ∈ layerIdeal O r n := by
      induction n with
      | zero => simp
      | succ n ih => exact h n (by omega) (ih (by omega))
    have h0 := hmem (r + 1) le_rfl
    rw [layerIdeal_eq_bot O (Nat.lt_succ_self r), Ideal.mem_bot] at h0
    exact hX h0
  have hs0 : 1 ≤ s := by
    by_contra h
    obtain rfl : s = 0 := by omega
    exact hs1 hX1
  refine ⟨s, ⟨hs0, hsr, hs, hs1⟩, fun t ⟨_, _, ht, ht1⟩ ↦ ?_⟩
  rcases lt_trichotomy t s with h | h | h
  · exact absurd (layerIdeal_antitone O r h hs) ht1
  · exact h
  · exact absurd (layerIdeal_antitone O r h ht) hs1

/-- `Λ_j` as an `O`-submodule of `R_r`. -/
def layerSubmodule (r j : ℕ) : Submodule O (LaurentSeries (Truncation O r)) where
  carrier := layerIdeal O r j
  add_mem' := Ideal.add_mem _
  zero_mem' := Ideal.zero_mem _
  smul_mem' b X hX := by
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ hX

/-- `Λ_{j + 1}` as an `O`-submodule of `Λ_j`. -/
def nextLayerSubmodule (r j : ℕ) : Submodule O (layerSubmodule O r j) :=
  (layerSubmodule O r (j + 1)).comap (layerSubmodule O r j).subtype

/-- The graded piece `Λ_j ⧸ Λ_{j + 1}`. -/
abbrev GradedLayer (r j : ℕ) : Type _ := layerSubmodule O r j ⧸ nextLayerSubmodule O r j

variable [IsPrincipalIdealRing O]

/-- `Λ_j` consists of the Laurent series with coefficients in `𝔪 ^ j`. -/
theorem mem_layerIdeal_iff {r j : ℕ} (X : LaurentSeries (Truncation O r)) :
    X ∈ layerIdeal O r j ↔ ∀ n, X.coeff n ∈ maximalIdeal (Truncation O r) ^ j :=
  mem_map_C_iff _ X

/-- `Λ_1` is the kernel of the reduction `R_r → κ((T))`. -/
theorem mem_layerIdeal_one_iff {r : ℕ} (X : LaurentSeries (Truncation O r)) :
    X ∈ layerIdeal O r 1 ↔ mapRingHom (residue O r) X = 0 := by
  rw [mem_layerIdeal_iff, pow_one, HahnSeries.ext_iff, funext_iff]
  simp only [mapRingHom_coeff, HahnSeries.coeff_zero, ← RingHom.mem_ker, ker_residue]

/-- If `P ∈ R_r` reduces to `T ^ p` over a residue field of characteristic `p`, then
`P' ∈ Λ_1`. -/
theorem derivative_mem_layerIdeal_one (p : ℕ) [CharP (ResidueField O) p] {r : ℕ}
    {P : LaurentSeries (Truncation O r)}
    (hP : mapRingHom (residue O r) P = HahnSeries.single (p : ℤ) 1) :
    derivative (Truncation O r) P ∈ layerIdeal O r 1 := by
  rw [mem_layerIdeal_one_iff, mapRingHom_derivative, hP, derivative_single, Int.cast_natCast,
    CharP.cast_eq_zero (ResidueField O) p, zero_mul, map_zero]

end

section Uniformizer

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private def uniformizer : O := Classical.choose (IsDiscreteValuationRing.exists_irreducible O)

private theorem irreducible_uniformizer : Irreducible (uniformizer O) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)

private theorem maximalIdeal_pow_eq_span (r j : ℕ) :
    maximalIdeal (Truncation O r) ^ j = Ideal.span {mk O r (uniformizer O) ^ j} := by
  rw [maximalIdeal_eq_map,
    congrArg (Ideal.map (mk O r)) (irreducible_uniformizer O).maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow]

private theorem layerIdeal_eq_span (r j : ℕ) :
    layerIdeal O r j = Ideal.span {HahnSeries.C (mk O r (uniformizer O) ^ j)} := by
  rw [layerIdeal, maximalIdeal_pow_eq_span, Ideal.map_span, Set.image_singleton]

private theorem C_mul_mem_layerIdeal (r j : ℕ) (Y : LaurentSeries (Truncation O r)) :
    HahnSeries.C (mk O r (uniformizer O) ^ j) * Y ∈ layerIdeal O r j := by
  rw [layerIdeal_eq_span]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

private theorem exists_eq_C_mul {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) :
    ∃ Y, X = HahnSeries.C (mk O r (uniformizer O) ^ j) * Y := by
  rw [layerIdeal_eq_span] at hX
  exact Ideal.mem_span_singleton.mp hX

private theorem pow_mul_mem_iff {r j : ℕ} (hj : j ≤ r) (y : Truncation O r) :
    mk O r (uniformizer O) ^ j * y ∈ maximalIdeal (Truncation O r) ^ (j + 1) ↔
      residue O r y = 0 := by
  obtain ⟨a, rfl⟩ := mk_surjective O r y
  rw [← map_pow, ← map_mul, mk_mem_maximalIdeal_pow_iff O (by omega), residue_mk,
    IsLocalRing.residue_eq_zero_iff, (irreducible_uniformizer O).maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero j (irreducible_uniformizer O).ne_zero)]

private theorem coeff_C_mul {R : Type*} [CommRing R] (a : R) (Y : LaurentSeries R) (n : ℤ) :
    (HahnSeries.C a * Y).coeff n = a * Y.coeff n := by
  simp

private theorem eq_zero_of_lt {r j : ℕ} (hj : r < j) {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) : X = 0 := by
  rwa [layerIdeal_eq_bot O hj, Ideal.mem_bot] at hX

private def residueLinear : LaurentSeries O →ₗ[O] LaurentSeries (ResidueField O) where
  __ := (mapRingHom (IsLocalRing.residue O)).toAddMonoidHom
  map_smul' b f := by
    change mapRingHom (IsLocalRing.residue O) (b • f) = b • mapRingHom (IsLocalRing.residue O) f
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, mapRingHom_C, Algebra.algebraMap_self,
      RingHom.id_apply, IsLocalRing.ResidueField.algebraMap_eq]

private theorem residueLinear_apply (f : LaurentSeries O) :
    residueLinear O f = mapRingHom (IsLocalRing.residue O) f := rfl

private theorem residueLinear_surjective : Function.Surjective (residueLinear O) :=
  mapRingHom_surjective _ IsLocalRing.residue_surjective

private theorem mem_ker_residueLinear (f : LaurentSeries O) :
    f ∈ LinearMap.ker (residueLinear O) ↔ ∀ n, IsLocalRing.residue O (f.coeff n) = 0 := by
  rw [LinearMap.mem_ker, residueLinear_apply, HahnSeries.ext_iff, funext_iff]
  simp only [mapRingHom_coeff, HahnSeries.coeff_zero]

private def gradedLift (r j : ℕ) : LaurentSeries O →ₗ[O] GradedLayer O r j where
  toFun f := Submodule.Quotient.mk
    ⟨HahnSeries.C (mk O r (uniformizer O) ^ j) * mapRingHom (mk O r) f,
      C_mul_mem_layerIdeal O r j _⟩
  map_add' f g := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (by simp only [map_add, mul_add, Submodule.coe_add])
  map_smul' b f := by
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext ?_
    simp only [SetLike.val_smul, smul_eq_C_mul, map_mul, mapRingHom_C, Algebra.algebraMap_self,
      RingHom.id_apply, Ideal.Quotient.algebraMap_eq]
    ring

private theorem gradedLift_apply (r j : ℕ) (f : LaurentSeries O) :
    gradedLift O r j f = Submodule.Quotient.mk
      ⟨HahnSeries.C (mk O r (uniformizer O) ^ j) * mapRingHom (mk O r) f,
        C_mul_mem_layerIdeal O r j _⟩ := rfl

private theorem gradedLift_surjective (r j : ℕ) : Function.Surjective (gradedLift O r j) := by
  intro x
  obtain ⟨⟨X, hX⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
  obtain ⟨f, rfl⟩ := mapRingHom_surjective _ (mk_surjective O r) Y
  exact ⟨f, rfl⟩

private theorem mem_ker_gradedLift {r j : ℕ} (hj : j ≤ r) (f : LaurentSeries O) :
    f ∈ LinearMap.ker (gradedLift O r j) ↔ ∀ n, IsLocalRing.residue O (f.coeff n) = 0 := by
  rw [LinearMap.mem_ker, gradedLift_apply, Submodule.Quotient.mk_eq_zero]
  change HahnSeries.C (mk O r (uniformizer O) ^ j) * mapRingHom (mk O r) f ∈
    layerIdeal O r (j + 1) ↔ _
  simp only [mem_layerIdeal_iff, coeff_C_mul, mapRingHom_coeff, pow_mul_mem_iff O hj,
    residue_mk]

private theorem ker_residueLinear_eq {r j : ℕ} (hj : j ≤ r) :
    LinearMap.ker (residueLinear O) = LinearMap.ker (gradedLift O r j) := by
  ext f
  rw [mem_ker_residueLinear, mem_ker_gradedLift O hj]

end Uniformizer

public section

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- For `j ≤ r`, the isomorphism `κ((T)) ≃ Λ_j ⧸ Λ_{j + 1}` induced by multiplication by `ϖ ^ j`,
for a uniformizer `ϖ` of `O` fixed once and for all (Yuan, §2.2). -/
def gradedLayerEquiv (r j : ℕ) (hj : j ≤ r) :
    LaurentSeries (ResidueField O) ≃ₗ[O] GradedLayer O r j :=
  ((residueLinear O).quotKerEquivOfSurjective (residueLinear_surjective O)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_residueLinear_eq O hj)).trans
      ((gradedLift O r j).quotKerEquivOfSurjective (gradedLift_surjective O r j)))

end

private theorem gradedLayerEquiv_residueLinear (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {r j : ℕ} (hj : j ≤ r) (f : LaurentSeries O) :
    gradedLayerEquiv O r j hj (residueLinear O f) = gradedLift O r j f := by
  simp only [gradedLayerEquiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

@[expose] public section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open Classical in
/-- The layer `ϖ⁻ʲ X ∈ κ((T))` of `X ∈ Λ_j`: the preimage of `X mod Λ_{j + 1}` under
`gradedLayerEquiv`, for `j ≤ r`. It is `0` if `X ∉ Λ_j` or `r < j`. -/
def layer {r : ℕ} (j : ℕ) (X : LaurentSeries (Truncation O r)) : LaurentSeries (ResidueField O) :=
  if h : j ≤ r ∧ X ∈ layerIdeal O r j then
    (gradedLayerEquiv O r j h.1).symm (Submodule.Quotient.mk ⟨X, h.2⟩)
  else 0

/-- On `Λ_j` with `j ≤ r`, `layer j` is the inverse of `gradedLayerEquiv`. -/
theorem gradedLayerEquiv_symm_mk {r j : ℕ} (hj : j ≤ r) {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) :
    (gradedLayerEquiv O r j hj).symm (Submodule.Quotient.mk ⟨X, hX⟩) = layer j X := by
  rw [layer, dite_eq_left ⟨hj, hX⟩]

/-- `layer j X = 0` for `X ∉ Λ_j`. -/
theorem layer_of_notMem {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∉ layerIdeal O r j) : layer j X = 0 := by
  rw [layer, dite_eq_right fun h ↦ hX h.2]

/-- `layer j = 0` for `j > r`. -/
theorem layer_of_lt {r j : ℕ} (hj : r < j) (X : LaurentSeries (Truncation O r)) :
    layer j X = 0 := by
  rw [layer, dite_eq_right fun h ↦ by omega]

@[simp]
theorem layer_zero {r : ℕ} (j : ℕ) : layer j (0 : LaurentSeries (Truncation O r)) = 0 := by
  rcases le_or_gt j r with hj | hj
  · rw [← gradedLayerEquiv_symm_mk hj (Ideal.zero_mem _)]
    exact (LinearEquiv.map_eq_zero_iff _).mpr rfl
  · exact layer_of_lt hj 0

end

private theorem layer_C_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {r j : ℕ} (hj : j ≤ r) (Y : LaurentSeries (Truncation O r)) :
    layer j (HahnSeries.C (mk O r (uniformizer O) ^ j) * Y) = mapRingHom (residue O r) Y := by
  rw [← gradedLayerEquiv_symm_mk hj (C_mul_mem_layerIdeal O r j Y)]
  apply (gradedLayerEquiv O r j hj).injective
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨f, rfl⟩ := mapRingHom_surjective _ (mk_surjective O r) Y
  rw [mapRingHom_residue_mapRingHom_mk, ← residueLinear_apply, gradedLayerEquiv_residueLinear,
    gradedLift_apply]

@[expose] public section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- For `X ∈ Λ_j`, `layer j X = 0` if and only if `X ∈ Λ_{j + 1}`. -/
theorem layer_eq_zero_iff {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) : layer j X = 0 ↔ X ∈ layerIdeal O r (j + 1) := by
  rcases le_or_gt j r with hj | hj
  · rw [← gradedLayerEquiv_symm_mk hj hX, LinearEquiv.map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero]
    rfl
  · obtain rfl := eq_zero_of_lt O hj hX
    simp only [layer_zero, Submodule.zero_mem]

theorem layer_ne_zero_iff {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) : layer j X ≠ 0 ↔ X ∉ layerIdeal O r (j + 1) :=
  (layer_eq_zero_iff hX).not

theorem layer_add {r j : ℕ} {X Y : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) (hY : Y ∈ layerIdeal O r j) :
    layer j (X + Y) = layer j X + layer j Y := by
  rcases le_or_gt j r with hj | hj
  · rw [← gradedLayerEquiv_symm_mk hj hX, ← gradedLayerEquiv_symm_mk hj hY,
      ← gradedLayerEquiv_symm_mk hj (Ideal.add_mem _ hX hY), ← map_add,
      ← Submodule.Quotient.mk_add]
    rfl
  · rw [layer_of_lt hj, layer_of_lt hj, layer_of_lt hj, add_zero]

theorem layer_neg {r j : ℕ} {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j) :
    layer j (-X) = -layer j X := by
  rcases le_or_gt j r with hj | hj
  · rw [← gradedLayerEquiv_symm_mk hj hX, ← gradedLayerEquiv_symm_mk hj (neg_mem hX),
      ← map_neg, ← Submodule.Quotient.mk_neg]
    rfl
  · rw [layer_of_lt hj, layer_of_lt hj, neg_zero]

theorem layer_sub {r j : ℕ} {X Y : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) (hY : Y ∈ layerIdeal O r j) :
    layer j (X - Y) = layer j X - layer j Y := by
  rw [sub_eq_add_neg, layer_add hX (neg_mem hY), layer_neg hY, sub_eq_add_neg]

/-- For `X ∈ Λ_j`, `layer j (X Z) = layer j X · Z̄`, where `Z̄` is the reduction of `Z` to
`κ((T))`. -/
theorem layer_mul {r j : ℕ} {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j)
    (Z : LaurentSeries (Truncation O r)) :
    layer j (X * Z) = layer j X * mapRingHom (residue O r) Z := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [mul_assoc, layer_C_mul hj, layer_C_mul hj, map_mul]
  · rw [layer_of_lt hj, layer_of_lt hj, zero_mul]

/-- For `X ∈ Λ_j`, the `n`-th coefficient of `layer j X` vanishes if and only if the `n`-th
coefficient of `X` lies in `𝔪 ^ (j + 1)`. -/
theorem coeff_layer_eq_zero_iff {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) (n : ℤ) :
    (layer j X).coeff n = 0 ↔ X.coeff n ∈ maximalIdeal (Truncation O r) ^ (j + 1) := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [layer_C_mul hj, mapRingHom_coeff, coeff_C_mul, pow_mul_mem_iff O hj]
  · obtain rfl := eq_zero_of_lt O hj hX
    simp only [layer_zero, HahnSeries.coeff_zero, Submodule.zero_mem]

/-- If `X ∈ Λ_j` and the `n`-th coefficient of `X` is `a b` with `a ∈ 𝔪 ^ j`, then the `n`-th
coefficient of `layer j X` is the constant term of `layer j a` times the residue of `b`. -/
theorem coeff_layer_eq_of_coeff_eq_mul {r j : ℕ} {X : LaurentSeries (Truncation O r)}
    (hX : X ∈ layerIdeal O r j) {n : ℤ} {a b : Truncation O r}
    (ha : a ∈ maximalIdeal (Truncation O r) ^ j) (h : X.coeff n = a * b) :
    (layer j X).coeff n = (layer j (HahnSeries.C a)).coeff 0 * residue O r b := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [maximalIdeal_pow_eq_span] at ha
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [coeff_C_mul, mul_assoc] at h
    rw [map_mul, layer_C_mul hj, layer_C_mul hj, mapRingHom_coeff, mapRingHom_C,
      HahnSeries.C_apply, HahnSeries.coeff_single_same, ← map_mul]
    have hmem := (pow_mul_mem_iff O hj (Y.coeff n - a' * b)).mp
      (by rw [mul_sub, h, sub_self]; exact zero_mem _)
    rwa [map_sub, sub_eq_zero] at hmem
  · rw [layer_of_lt hj, layer_of_lt hj, HahnSeries.coeff_zero, HahnSeries.coeff_zero, zero_mul]

/-- If an algebra endomorphism `E` of `R_r` reduces to the endomorphism `E'` of `κ((T))`, then
`layer j (E X) = E' (layer j X)` for `X ∈ Λ_j`. -/
theorem layer_algHom {r j : ℕ}
    (E : LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (E' : LaurentSeries (ResidueField O) →ₐ[ResidueField O] LaurentSeries (ResidueField O))
    (hE : ∀ Y, mapRingHom (residue O r) (E Y) = E' (mapRingHom (residue O r) Y))
    {X : LaurentSeries (Truncation O r)} (hX : X ∈ layerIdeal O r j) :
    layer j (E X) = E' (layer j X) := by
  rcases le_or_gt j r with hj | hj
  · obtain ⟨Y, rfl⟩ := exists_eq_C_mul O hX
    rw [map_mul, algHom_C, layer_C_mul hj, layer_C_mul hj, hE]
  · rw [layer_of_lt hj, layer_of_lt hj, map_zero]

end

end FalseTateNonliftability.Truncation
