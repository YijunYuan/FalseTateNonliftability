/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Degree
public import FontaineWintenberger.APF.Tower.AlgebraicResidue

/-!
# Totally ramified extensions and intermediate fields with the same residue field

Let `K` be a complete discretely valued field and `L/K` an algebraic extension, possibly infinite.
The extension `L/K` is totally ramified if the residue field of the integral closure of `𝒪[K]`
in `L` is `𝓀[K]`, that is, if the residue map `𝓀[K] → 𝓀_L` is surjective. Every subextension of
a totally ramified extension is totally ramified. A finite separable extension `L/K` is totally
ramified if and only if its residue degree is `1`, if and only if its ramification index is
`[L : K]`.

Let `Ω/K₀` be an algebraic extension of a complete discretely valued field. Two intermediate fields
`E` and `F` of `Ω/K₀` have the same residue field if the residue fields of the integral closures of
`𝒪[K₀]` in `E` and in `F` have the same image in the residue field of `Ω`. This is the condition
"`F` has the same residue field as `K`" in Berger's definition of `F`-liftable actions. An
intermediate field `F` has the same residue field as `K₀` if and only if `F/K₀` is totally
ramified.

## Main definitions

* `FontaineWintenberger.IsTotallyRamified K L`: the algebraic extension `L/K` is totally ramified.
* `IntermediateField.HasSameResidueField E F`: the intermediate fields `E` and `F` of `Ω/K₀` have
  the same residue field.
* `IntermediateField.HasSameResidueField.residueFieldEquiv E F`: the isomorphism over `𝓀[K₀]` of
  the residue fields of `E` and `F` compatible with their embeddings into the residue field of `Ω`.

## Main results

* `FontaineWintenberger.isTotallyRamified_iff_finrank_residueField_eq_one`,
  `FontaineWintenberger.isTotallyRamified_iff_ramificationIdx_eq_finrank`: a finite separable
  extension is totally ramified if and only if `f(L/K) = 1`, if and only if `e(L/K) = [L : K]`.
* `FontaineWintenberger.IsTotallyRamified.of_algHom`: a subextension of a totally ramified
  extension is totally ramified.
* `IntermediateField.hasSameResidueField_bot_iff`: `F` has the same residue field as `K₀` if and
  only if `F/K₀` is totally ramified.

## Implementation notes

The total ramification and same residue field interfaces extend FontaineWintenberger here.
The integral closure and spectral residue field maps are supplied by
`FontaineWintenberger.APF.Tower.AlgebraicResidue`. The abbreviation
`integralClosureResidueField` fixes their ring and algebra structures for intermediate fields.

## References

* Serre, *Local Fields*, Chapter II, §2 (`[L : K] = e f` over a complete discretely valued field).
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014) (the residue field
  condition in the definition of `F`-liftable actions).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

/-- The residue field of the integral closure of `𝒪[K]` in an algebraic extension `L/K`. -/
abbrev integralClosureResidueField (K : Type*) [NontriviallyNormedField K]
    [IsCompleteDiscreteValuedField K] (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] : Type _ :=
  IsLocalRing.ResidueField (integralClosure 𝒪[K] L)

section TotallyRamified

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

/-- An algebraic extension `L/K`, possibly infinite, is totally ramified if the residue field of
the integral closure of `𝒪[K]` in `L` is `𝓀[K]`: the residue map `𝓀[K] → 𝓀_L` is surjective. -/
class IsTotallyRamified (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] : Prop where
  algebraMap_surjective : Function.Surjective (algebraMap 𝓀[K] (integralClosureResidueField K L))

section Algebraic

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- An algebraic extension `L/K` is totally ramified if and only if the residue map from `𝓀[K]`
to the residue field of the spectral integer ring of `L` is surjective. -/
theorem isTotallyRamified_iff_surjective_spectralIntegerRing :
    IsTotallyRamified K L ↔ Function.Surjective
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (spectralIntegerRing K L))) := by
  let e := integralClosureSpectralResidueEquiv K (L := L)
  constructor
  · intro h z
    obtain ⟨a, ha⟩ := h.algebraMap_surjective (e.symm z)
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩
  · intro h
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨a, ha⟩ := h (e z)
    exact ⟨a, e.injective (by rw [e.commutes, ha])⟩

end Algebraic

section Embedding

variable {K} {E L : Type*} [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L]

/-- For a `K`-embedding `i : E → L`, the residue field of `E` has the same image in the residue
field of `L` as `𝓀[K]` if and only if `E/K` is totally ramified. -/
theorem range_integralClosureResidueInclusion_eq_bot_iff (i : E →ₐ[K] L) :
    (integralClosureResidueInclusion K i).range = ⊥ ↔ IsTotallyRamified K E := by
  let f := integralClosureResidueInclusion K i
  constructor
  · intro h
    refine ⟨fun z ↦ ?_⟩
    have hz : f z ∈ (⊥ : Subalgebra 𝓀[K] _) := h ▸ f.mem_range_self z
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hz
    exact ⟨a, f.injective ((f.commutes a).trans ha)⟩
  · intro h
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨z, rfl⟩ := f.mem_range.mp hx
    obtain ⟨a, rfl⟩ := h.algebraMap_surjective z
    rw [f.commutes]
    exact Subalgebra.algebraMap_mem _ a

/-- A subextension of a totally ramified extension is totally ramified. -/
theorem IsTotallyRamified.of_algHom [IsTotallyRamified K L] (i : E →ₐ[K] L) :
    IsTotallyRamified K E := by
  refine ⟨fun z ↦ ?_⟩
  let f := integralClosureResidueInclusion K i
  obtain ⟨a, ha⟩ := IsTotallyRamified.algebraMap_surjective (K := K) (L := L) (f z)
  exact ⟨a, f.injective ((f.commutes a).trans ha)⟩

/-- Total ramification is invariant under `K`-isomorphisms. -/
theorem IsTotallyRamified.of_algEquiv [IsTotallyRamified K L] (e : E ≃ₐ[K] L) :
    IsTotallyRamified K E :=
  .of_algHom e.toAlgHom

/-- Every intermediate field of a totally ramified extension is totally ramified over the base. -/
instance IsTotallyRamified.intermediateField [IsTotallyRamified K L] (E : IntermediateField K L) :
    IsTotallyRamified K E :=
  .of_algHom E.val

end Embedding

section Finite

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- A finite separable extension `L/K` is totally ramified if and only if its residue degree
`f(L/K)` is `1`. -/
theorem isTotallyRamified_iff_finrank_residueField_eq_one :
    IsTotallyRamified K L ↔
      Module.finrank 𝓀[K] (IsLocalRing.ResidueField (spectralIntegerRing K L)) = 1 := by
  rw [isTotallyRamified_iff_surjective_spectralIntegerRing,
    Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact ⟨fun h ↦ ⟨(algebraMap 𝓀[K] (IsLocalRing.ResidueField (spectralIntegerRing K L))).injective,
    h⟩, fun h ↦ h.2⟩

/-- A finite separable extension `L/K` is totally ramified if and only if its ramification index
`e(L/K)` is `[L : K]`. -/
theorem isTotallyRamified_iff_ramificationIdx_eq_finrank :
    IsTotallyRamified K L ↔
      (IsLocalRing.maximalIdeal (spectralIntegerRing K L)).ramificationIdx 𝒪[K] =
        Module.finrank K L := by
  have h := extensionValuationSubring_ramificationIdx_mul_residueDegree K L
    (spectralValuation K L)
  rw [isTotallyRamified_iff_finrank_residueField_eq_one]
  constructor
  · intro hf
    rwa [hf, mul_one] at h
  · intro he
    rw [he] at h
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos (h.trans (mul_one _).symm)

/-- The residue degree of a finite separable totally ramified extension is `1`. -/
theorem IsTotallyRamified.finrank_residueField_eq_one [IsTotallyRamified K L] :
    Module.finrank 𝓀[K] (IsLocalRing.ResidueField (spectralIntegerRing K L)) = 1 :=
  (isTotallyRamified_iff_finrank_residueField_eq_one K L).mp ‹_›

/-- The ramification index of a finite separable totally ramified extension `L/K` is
`[L : K]`. -/
theorem IsTotallyRamified.ramificationIdx_eq_finrank [IsTotallyRamified K L] :
    (IsLocalRing.maximalIdeal (spectralIntegerRing K L)).ramificationIdx 𝒪[K] =
      Module.finrank K L :=
  (isTotallyRamified_iff_ramificationIdx_eq_finrank K L).mp ‹_›

end Finite

/-- The trivial extension `K/K` is totally ramified. -/
instance isTotallyRamified_self : IsTotallyRamified K K := by
  have h := extensionValuationSubring_ramificationIdx_mul_residueDegree K K
    (spectralValuation K K)
  rw [Module.finrank_self] at h
  exact (isTotallyRamified_iff_finrank_residueField_eq_one K K).mpr
    (Nat.eq_one_of_mul_eq_one_left h)

/-- The bottom intermediate field of any extension of `K` is totally ramified over `K`. -/
instance isTotallyRamified_bot (L : Type*) [Field L] [Algebra K L] :
    IsTotallyRamified K (⊥ : IntermediateField K L) :=
  .of_algEquiv (IntermediateField.botEquiv K L)

end TotallyRamified

end FontaineWintenberger

namespace IntermediateField

open FontaineWintenberger

variable {K₀ Ω : Type*} [NontriviallyNormedField K₀] [IsCompleteDiscreteValuedField K₀]
    [Field Ω] [Algebra K₀ Ω] [Algebra.IsAlgebraic K₀ Ω]

/-- Two intermediate fields `E` and `F` of an algebraic extension `Ω/K₀` have the same residue
field if the residue fields of the integral closures of `𝒪[K₀]` in `E` and in `F` have the same
image in the residue field of the integral closure of `𝒪[K₀]` in `Ω`. This is Berger's condition
"`F` has the same residue field as `E`". -/
class HasSameResidueField (E F : IntermediateField K₀ Ω) : Prop where
  range_eq : (integralClosureResidueInclusion K₀ E.val).range =
    (integralClosureResidueInclusion K₀ F.val).range

namespace HasSameResidueField

variable {E F G : IntermediateField K₀ Ω}

instance refl (E : IntermediateField K₀ Ω) : HasSameResidueField E E :=
  ⟨rfl⟩

theorem symm [HasSameResidueField E F] : HasSameResidueField F E :=
  ⟨range_eq.symm⟩

theorem trans [HasSameResidueField E F] [HasSameResidueField F G] : HasSameResidueField E G :=
  ⟨(range_eq (E := E) (F := F)).trans range_eq⟩

variable (E F) in
/-- The isomorphism over `𝓀[K₀]` of the residue fields of intermediate fields `E` and `F` with the
same residue field, through their common image in the residue field of `Ω`. -/
def residueFieldEquiv [HasSameResidueField E F] :
    integralClosureResidueField K₀ E ≃ₐ[𝓀[K₀]] integralClosureResidueField K₀ F :=
  (AlgEquiv.ofInjective _ (integralClosureResidueInclusion K₀ E.val).injective).trans
    ((Subalgebra.equivOfEq _ _ range_eq).trans
      (AlgEquiv.ofInjective _ (integralClosureResidueInclusion K₀ F.val).injective).symm)

/-- The isomorphism `residueFieldEquiv E F` is compatible with the embeddings of the residue fields
of `E` and `F` into the residue field of `Ω`. -/
@[simp]
theorem integralClosureResidueInclusion_residueFieldEquiv [HasSameResidueField E F]
    (z : integralClosureResidueField K₀ E) :
    integralClosureResidueInclusion K₀ F.val (residueFieldEquiv E F z) =
      integralClosureResidueInclusion K₀ E.val z :=
  congrArg Subtype.val
    ((AlgEquiv.ofInjective _ (integralClosureResidueInclusion K₀ F.val).injective).apply_symm_apply
      (Subalgebra.equivOfEq _ _ (range_eq (E := E) (F := F))
        (AlgEquiv.ofInjective _ (integralClosureResidueInclusion K₀ E.val).injective z)))

theorem integralClosureResidueInclusion_comp_residueFieldEquiv [HasSameResidueField E F] :
    (integralClosureResidueInclusion K₀ F.val).comp (residueFieldEquiv E F).toAlgHom =
      integralClosureResidueInclusion K₀ E.val :=
  AlgHom.ext fun z ↦ integralClosureResidueInclusion_residueFieldEquiv z

end HasSameResidueField

theorem hasSameResidueField_comm {E F : IntermediateField K₀ Ω} :
    HasSameResidueField E F ↔ HasSameResidueField F E :=
  ⟨fun _ ↦ .symm, fun _ ↦ .symm⟩

/-- An intermediate field `F` of `Ω/K₀` has the same residue field as `K₀` if and only if `F/K₀`
is totally ramified. -/
theorem hasSameResidueField_bot_iff (F : IntermediateField K₀ Ω) :
    HasSameResidueField ⊥ F ↔ IsTotallyRamified K₀ F := by
  rw [← range_integralClosureResidueInclusion_eq_bot_iff F.val]
  have h := (range_integralClosureResidueInclusion_eq_bot_iff
    (⊥ : IntermediateField K₀ Ω).val).mpr inferInstance
  exact ⟨fun hs ↦ hs.range_eq.symm.trans h, fun hF ↦ ⟨h.trans hF.symm⟩⟩

/-- An intermediate field `F` of `Ω/K₀` has the same residue field as `K₀` if and only if `F/K₀`
is totally ramified. -/
theorem hasSameResidueField_bot_right_iff (F : IntermediateField K₀ Ω) :
    HasSameResidueField F ⊥ ↔ IsTotallyRamified K₀ F :=
  hasSameResidueField_comm.trans (hasSameResidueField_bot_iff F)

instance hasSameResidueField_bot (F : IntermediateField K₀ Ω) [IsTotallyRamified K₀ F] :
    HasSameResidueField ⊥ F :=
  (hasSameResidueField_bot_iff F).mpr ‹_›

instance hasSameResidueField_bot_right (F : IntermediateField K₀ Ω) [IsTotallyRamified K₀ F] :
    HasSameResidueField F ⊥ :=
  (hasSameResidueField_bot_right_iff F).mpr ‹_›

/-- Intermediate fields with the same residue field are totally ramified over `K₀` together. -/
theorem HasSameResidueField.isTotallyRamified_iff {E F : IntermediateField K₀ Ω}
    [HasSameResidueField E F] : IsTotallyRamified K₀ E ↔ IsTotallyRamified K₀ F := by
  rw [← hasSameResidueField_bot_iff, ← hasSameResidueField_bot_iff]
  have := HasSameResidueField.symm (E := E) (F := F)
  exact ⟨fun _ ↦ .trans (F := E), fun _ ↦ .trans (F := F)⟩

end IntermediateField
