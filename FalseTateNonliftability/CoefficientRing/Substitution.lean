/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.Truncation
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition

/-!
# Substitution in the coefficient ring `A`

Let `O` be a local principal ideal ring with maximal ideal `𝔪` and residue field `κ`, for
instance the ring of integers of a finite extension of `ℚ_p`, and let `A` be the `𝔪`-adic
completion of `O((T))` (`FalseTateNonliftability.CoefficientRing O`). Over each truncation
`O ⧸ 𝔪 ^ (r + 1)` substitution is `LaurentSeries.subst`.

An element `G ∈ A` is admissible if its image in `κ((T))` has finite positive order; then so
are its reductions modulo every `𝔪 ^ (r + 1)`. The substitutions `f ↦ f(G)` on the rings
`(O ⧸ 𝔪 ^ (r + 1))((T))` are compatible, and their inverse limit is an `O`-algebra endomorphism
`f ↦ f(G)` of `A` sending `T` to `G`. It is the only `O`-algebra endomorphism of `A` sending `T`
to `G` that induces a `T`-adically continuous endomorphism of every `(O ⧸ 𝔪 ^ (r + 1))((T))`.
Composition of substitutions is substitution at the composite, and a power series `H` over `O`
with `H(0) = 0` and `H'(0)` a unit gives an automorphism `f ↦ f(H)` of `A`, whose inverse is
substitution at the compositional inverse `H^{∘-1}`.

## Main definitions

* `CoefficientRing.X`: the variable `T` of `A`.
* `CoefficientRing.IsAdmissible G`: the image of `G` in `κ((T))` has finite positive order.
* `CoefficientRing.subst G`: the substitution `f ↦ f(G)`; the identity if `G` is not admissible.
* `CoefficientRing.substEquiv H`: the automorphism `f ↦ f(H)` for a power series `H` over `O`
  with `H(0) = 0` and `H'(0)` a unit; the identity for every other `H`.

## Main results

* `CoefficientRing.reduction_subst`, `CoefficientRing.residue_subst`: substitution commutes with
  reduction modulo `𝔪 ^ (r + 1)` and with reduction to `κ((T))`.
* `CoefficientRing.subst_X`: `T(G) = G`.
* `CoefficientRing.subst_unique`: uniqueness of substitution.
* `CoefficientRing.subst_comp_subst`: `f(G)(H) = f(G(H))`.
* `CoefficientRing.subst_algebraMap_powerSeries`: on power series over `O`, substitution is
  `PowerSeries.subst`.
* `CoefficientRing.substEquiv_symm`: the inverse of `f ↦ f(H)` is `f ↦ f(H^{∘-1})`.

## References

* Yuan, Lemma 2.1.
-/

public section

noncomputable section

namespace LaurentSeries

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]
  [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsPrincipalIdealRing S]

/-- Substitution commutes with coefficient maps: `φ(f(G)) = (φ f)(φ G)` for every `G`. -/
theorem mapRingHom_subst' (φ : R →+* S) (G f : LaurentSeries R) :
    mapRingHom φ (subst G f) = subst (mapRingHom φ G) (mapRingHom φ f) := by
  by_cases hG : IsAdmissible G
  · exact mapRingHom_subst φ hG f
  · rw [subst_of_not_isAdmissible hG,
      subst_of_not_isAdmissible (mt (isAdmissible_mapRingHom_iff φ G).mp hG), AlgHom.id_apply,
      AlgHom.id_apply]

end LaurentSeries

namespace FalseTateNonliftability.CoefficientRing

open LaurentSeries

private theorem constantCoeff_map_eq_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {H : PowerSeries R} (hH : H.constantCoeff = 0) : (H.map φ).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hH, map_zero]

private theorem isUnit_coeff_one_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {H : PowerSeries R} (hl : IsUnit (H.coeff 1)) : IsUnit ((H.map φ).coeff 1) := by
  rw [PowerSeries.coeff_map]
  exact hl.map φ

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- The variable `T` of `A`. -/
@[expose] def X : CoefficientRing O :=
  algebraMap (LaurentSeries O) (CoefficientRing O) (HahnSeries.single 1 1)

@[simp]
theorem reduction_X (r : ℕ) : reduction O r X = HahnSeries.single 1 1 := by
  rw [X, reduction_algebraMap_laurentSeries, mapRingHom_single, map_one]

@[simp]
theorem residue_X : residue O X = HahnSeries.single 1 1 := by
  rw [X, residue_algebraMap_laurentSeries, mapRingHom_single, map_one]

theorem algebraMap_powerSeries_X :
    algebraMap (PowerSeries O) (CoefficientRing O) PowerSeries.X = X := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries O) (LaurentSeries O), coe_algebraMap,
    HahnSeries.ofPowerSeries_X, X]

@[simp]
theorem residue_algebraMap_powerSeries (P : PowerSeries O) :
    residue O (algebraMap (PowerSeries O) (CoefficientRing O) P) =
      HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (IsLocalRing.residue O) P) := by
  rw [IsScalarTower.algebraMap_apply (PowerSeries O) (LaurentSeries O),
    residue_algebraMap_laurentSeries, coe_algebraMap, mapRingHom_ofPowerSeries]

/-- An element `G` of `A` is admissible if its image in `κ((T))` has finite positive order. -/
@[expose] def IsAdmissible (G : CoefficientRing O) : Prop :=
  LaurentSeries.IsAdmissible (residue O G)

theorem isAdmissible_iff_isAdmissible_residue (G : CoefficientRing O) :
    IsAdmissible G ↔ LaurentSeries.IsAdmissible (residue O G) :=
  Iff.rfl

theorem isAdmissible_iff (G : CoefficientRing O) :
    IsAdmissible G ↔ ∃ a : ℤ, 0 < a ∧ (residue O G).orderTop = a :=
  LaurentSeries.isAdmissible_iff _

theorem isAdmissible_X : IsAdmissible (X : CoefficientRing O) := by
  rw [isAdmissible_iff_isAdmissible_residue, residue_X]
  exact LaurentSeries.isAdmissible_X

/-- A power series `H` over `O` with `H(0) = 0` and `H'(0)` a unit is admissible. -/
theorem isAdmissible_algebraMap_powerSeries {H : PowerSeries O} (hH : H.constantCoeff = 0)
    (hl : IsUnit (H.coeff 1)) :
    IsAdmissible (algebraMap (PowerSeries O) (CoefficientRing O) H) := by
  rw [isAdmissible_iff_isAdmissible_residue, residue_algebraMap_powerSeries]
  exact isAdmissible_ofPowerSeries (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)

variable [IsPrincipalIdealRing O]

/-- An element of `A` is admissible if and only if its reduction modulo `𝔪 ^ (r + 1)` is. -/
theorem isAdmissible_iff_reduction (r : ℕ) (G : CoefficientRing O) :
    IsAdmissible G ↔ LaurentSeries.IsAdmissible (reduction O r G) := by
  rw [isAdmissible_iff_isAdmissible_residue, ← mapRingHom_residue_reduction O r,
    isAdmissible_mapRingHom_iff]

private theorem mapRingHom_factor_subst_reduction (G : CoefficientRing O) {s r : ℕ}
    (hsr : s ≤ r) (f : CoefficientRing O) :
    mapRingHom (Truncation.factor O hsr)
        (LaurentSeries.subst (reduction O r G) (reduction O r f)) =
      LaurentSeries.subst (reduction O s G) (reduction O s f) := by
  rw [mapRingHom_subst', mapRingHom_factor_reduction, mapRingHom_factor_reduction]

private theorem mapRingHom_factor_comp_subst_reduction (G : CoefficientRing O) {s r : ℕ}
    (hsr : s ≤ r) :
    (mapRingHom (Truncation.factor O hsr)).comp
        ((LaurentSeries.subst (reduction O r G)).toRingHom.comp (reduction O r)) =
      (LaurentSeries.subst (reduction O s G)).toRingHom.comp (reduction O s) :=
  RingHom.ext (mapRingHom_factor_subst_reduction G hsr)

private def substRingHom (G : CoefficientRing O) : CoefficientRing O →+* CoefficientRing O :=
  lift (fun r ↦ (LaurentSeries.subst (reduction O r G)).toRingHom.comp (reduction O r))
    fun hsr ↦ mapRingHom_factor_comp_subst_reduction G hsr

private theorem reduction_substRingHom (G : CoefficientRing O) (r : ℕ) (f : CoefficientRing O) :
    reduction O r (substRingHom G f) = LaurentSeries.subst (reduction O r G) (reduction O r f) :=
  reduction_lift _ (fun hsr ↦ mapRingHom_factor_comp_subst_reduction G hsr) r f

private theorem substRingHom_algebraMap (G : CoefficientRing O) (b : O) :
    substRingHom G (algebraMap O (CoefficientRing O) b) = algebraMap O (CoefficientRing O) b :=
  ext_reduction O fun r ↦ by rw [reduction_substRingHom, reduction_algebraMap, subst_C]

/-- Substitution `f ↦ f(G)` of `G ∈ A` for the variable: the `O`-algebra endomorphism of `A`
that reduces modulo every `𝔪 ^ (r + 1)` to substitution of the reduction of `G`
(`reduction_subst`). It is the identity if `G` is not admissible. -/
def subst (G : CoefficientRing O) : CoefficientRing O →ₐ[O] CoefficientRing O :=
  { substRingHom G with commutes' := substRingHom_algebraMap G }

/-- Substitution commutes with reduction modulo `𝔪 ^ (r + 1)`. -/
@[simp]
theorem reduction_subst (G : CoefficientRing O) (r : ℕ) (f : CoefficientRing O) :
    reduction O r (subst G f) = LaurentSeries.subst (reduction O r G) (reduction O r f) :=
  reduction_substRingHom G r f

/-- Substitution commutes with reduction to `κ((T))`. -/
@[simp]
theorem residue_subst (G f : CoefficientRing O) :
    residue O (subst G f) = LaurentSeries.subst (residue O G) (residue O f) := by
  rw [← mapRingHom_residue_reduction O 0, reduction_subst,
    mapRingHom_subst' (Truncation.residue O 0)]
  simp only [mapRingHom_residue_reduction]

theorem subst_of_not_isAdmissible {G : CoefficientRing O} (hG : ¬ IsAdmissible G) :
    subst G = AlgHom.id O _ :=
  AlgHom.ext fun f ↦ ext_reduction O fun r ↦ by
    rw [reduction_subst, LaurentSeries.subst_of_not_isAdmissible
      (mt (isAdmissible_iff_reduction r G).mpr hG), AlgHom.id_apply, AlgHom.id_apply]

@[simp]
theorem subst_X {G : CoefficientRing O} (hG : IsAdmissible G) : subst G X = G :=
  ext_reduction O fun r ↦ by
    rw [reduction_subst, reduction_X,
      LaurentSeries.subst_X ((isAdmissible_iff_reduction r G).mp hG)]

/-- Substitution of the variable is the identity. -/
theorem subst_X_left : subst (X : CoefficientRing O) = AlgHom.id O _ :=
  AlgHom.ext fun f ↦ ext_reduction O fun r ↦ by
    rw [reduction_subst, reduction_X, subst_X_left_apply, AlgHom.id_apply]

@[simp]
theorem subst_X_left_apply (f : CoefficientRing O) : subst X f = f := by
  rw [subst_X_left, AlgHom.id_apply]

/-- `subst G` is the only `O`-algebra endomorphism of `A` sending `T` to `G` that induces, modulo
every `𝔪 ^ (r + 1)`, an endomorphism of `(O ⧸ 𝔪 ^ (r + 1))((T))` continuous for the `T`-adic
topology. -/
theorem subst_unique {G : CoefficientRing O} (hG : IsAdmissible G)
    (F : CoefficientRing O →ₐ[O] CoefficientRing O)
    (Φ : (r : ℕ) →
      LaurentSeries (Truncation O r) →ₐ[Truncation O r] LaurentSeries (Truncation O r))
    (hΦ : ∀ r, @Continuous _ _ (orderTopology _) (orderTopology _) (Φ r))
    (hF : ∀ r f, reduction O r (F f) = Φ r (reduction O r f)) (hX : F X = G) :
    F = subst G := by
  have hΦG (r : ℕ) : Φ r = LaurentSeries.subst (reduction O r G) :=
    LaurentSeries.subst_unique ((isAdmissible_iff_reduction r G).mp hG) (Φ r) (hΦ r)
      (by rw [← reduction_X (O := O) r, ← hF, hX])
  exact AlgHom.ext fun f ↦ ext_reduction O fun r ↦ by rw [hF, hΦG, reduction_subst]

/-- If `G` and `H` are admissible, so is `G(H)`. -/
theorem IsAdmissible.subst {G H : CoefficientRing O} (hG : IsAdmissible G)
    (hH : IsAdmissible H) : IsAdmissible (CoefficientRing.subst H G) := by
  rw [isAdmissible_iff_isAdmissible_residue, residue_subst]
  exact LaurentSeries.IsAdmissible.subst hG hH

/-- Composition of substitutions: `f(G)(H) = f(G(H))`. -/
theorem subst_comp_subst {G H : CoefficientRing O} (hG : IsAdmissible G) (hH : IsAdmissible H) :
    (subst H).comp (subst G) = subst (subst H G) :=
  AlgHom.ext fun f ↦ ext_reduction O fun r ↦ by
    simp only [AlgHom.comp_apply, reduction_subst]
    exact subst_comp_subst_apply ((isAdmissible_iff_reduction r G).mp hG)
      ((isAdmissible_iff_reduction r H).mp hH) _

theorem subst_comp_subst_apply {G H : CoefficientRing O} (hG : IsAdmissible G)
    (hH : IsAdmissible H) (f : CoefficientRing O) :
    subst H (subst G f) = subst (subst H G) f :=
  AlgHom.congr_fun (subst_comp_subst hG hH) f

/-- On power series, substitution of a power series `P` over `O` with `P(0) = 0` is
`PowerSeries.subst`. -/
theorem subst_algebraMap_powerSeries {P : PowerSeries O} (hP : P.constantCoeff = 0)
    (hadm : IsAdmissible (algebraMap (PowerSeries O) (CoefficientRing O) P))
    (f : PowerSeries O) :
    subst (algebraMap (PowerSeries O) (CoefficientRing O) P)
        (algebraMap (PowerSeries O) (CoefficientRing O) f) =
      algebraMap (PowerSeries O) (CoefficientRing O) (f.subst P) :=
  ext_reduction O fun r ↦ by
    have hadm' := (isAdmissible_iff_reduction r _).mp hadm
    rw [reduction_algebraMap_powerSeries] at hadm'
    rw [reduction_subst, reduction_algebraMap_powerSeries, reduction_algebraMap_powerSeries,
      reduction_algebraMap_powerSeries, subst_ofPowerSeries (constantCoeff_map_eq_zero _ hP) hadm']
    exact congrArg _ (PowerSeries.map_subst (.of_constantCoeff_zero' hP) f).symm

section SubstEquiv

variable {H : PowerSeries O}

private theorem subst_comp_subst_compInv (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    (subst (algebraMap (PowerSeries O) (CoefficientRing O) H)).comp
        (subst (algebraMap (PowerSeries O) (CoefficientRing O) H.compInv)) =
      AlgHom.id O _ := by
  rw [subst_comp_subst (isAdmissible_algebraMap_powerSeries (PowerSeries.constantCoeff_compInv H)
      (PowerSeries.isUnit_coeff_one_compInv H)) (isAdmissible_algebraMap_powerSeries hH hl),
    subst_algebraMap_powerSeries hH (isAdmissible_algebraMap_powerSeries hH hl),
    PowerSeries.subst_compInv_left hH hl, algebraMap_powerSeries_X, subst_X_left]

private theorem subst_compInv_comp_subst (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    (subst (algebraMap (PowerSeries O) (CoefficientRing O) H.compInv)).comp
        (subst (algebraMap (PowerSeries O) (CoefficientRing O) H)) =
      AlgHom.id O _ := by
  have hinv := isAdmissible_algebraMap_powerSeries (PowerSeries.constantCoeff_compInv H)
    (PowerSeries.isUnit_coeff_one_compInv H)
  rw [subst_comp_subst (isAdmissible_algebraMap_powerSeries hH hl) hinv,
    subst_algebraMap_powerSeries (PowerSeries.constantCoeff_compInv H) hinv,
    PowerSeries.subst_compInv_right hH hl, algebraMap_powerSeries_X, subst_X_left]

open scoped Classical in
/-- The automorphism `f ↦ f(H)` of `A` for a power series `H` over `O` with `H(0) = 0` and
`H'(0)` a unit; its inverse is `f ↦ f(H^{∘-1})`. For every other `H` this is the identity. -/
def substEquiv (H : PowerSeries O) : CoefficientRing O ≃ₐ[O] CoefficientRing O :=
  if h : H.constantCoeff = 0 ∧ IsUnit (H.coeff 1) then
    AlgEquiv.ofAlgHom (subst (algebraMap (PowerSeries O) (CoefficientRing O) H))
      (subst (algebraMap (PowerSeries O) (CoefficientRing O) H.compInv))
      (subst_comp_subst_compInv h.1 h.2) (subst_compInv_comp_subst h.1 h.2)
  else AlgEquiv.refl

theorem substEquiv_of_not (h : ¬ (H.constantCoeff = 0 ∧ IsUnit (H.coeff 1))) :
    substEquiv H = AlgEquiv.refl :=
  dite_eq_right h

theorem substEquiv_apply (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (f : CoefficientRing O) :
    substEquiv H f = subst (algebraMap (PowerSeries O) (CoefficientRing O) H) f := by
  rw [substEquiv, dite_eq_left ⟨hH, hl⟩]
  rfl

theorem substEquiv_symm_apply (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (f : CoefficientRing O) :
    (substEquiv H).symm f = subst (algebraMap (PowerSeries O) (CoefficientRing O) H.compInv) f := by
  rw [substEquiv, dite_eq_left ⟨hH, hl⟩]
  rfl

/-- The inverse of `f ↦ f(H)` is `f ↦ f(H^{∘-1})`. -/
theorem substEquiv_symm (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    (substEquiv H).symm = substEquiv H.compInv :=
  AlgEquiv.ext fun f ↦ by
    rw [substEquiv_symm_apply hH hl, substEquiv_apply (PowerSeries.constantCoeff_compInv H)
      (PowerSeries.isUnit_coeff_one_compInv H)]

theorem substEquiv_X (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) :
    substEquiv H X = algebraMap (PowerSeries O) (CoefficientRing O) H := by
  rw [substEquiv_apply hH hl, subst_X (isAdmissible_algebraMap_powerSeries hH hl)]

theorem reduction_substEquiv (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (r : ℕ)
    (f : CoefficientRing O) :
    reduction O r (substEquiv H f) =
      LaurentSeries.substEquiv (H.map (Truncation.mk O r)) (reduction O r f) := by
  rw [substEquiv_apply hH hl, reduction_subst, reduction_algebraMap_powerSeries,
    LaurentSeries.substEquiv_apply (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)]

theorem reduction_substEquiv_symm (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1)) (r : ℕ)
    (f : CoefficientRing O) :
    reduction O r ((substEquiv H).symm f) =
      (LaurentSeries.substEquiv (H.map (Truncation.mk O r))).symm (reduction O r f) := by
  rw [substEquiv_symm_apply hH hl, reduction_subst, reduction_algebraMap_powerSeries,
    LaurentSeries.substEquiv_symm_apply (constantCoeff_map_eq_zero _ hH)
      (isUnit_coeff_one_map _ hl), ← PowerSeries.compInv_eq_substInvOfIsUnit,
    PowerSeries.map_compInv _ hH hl]

theorem residue_substEquiv (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (f : CoefficientRing O) :
    residue O (substEquiv H f) =
      LaurentSeries.substEquiv (H.map (IsLocalRing.residue O)) (residue O f) := by
  rw [substEquiv_apply hH hl, residue_subst, residue_algebraMap_powerSeries,
    LaurentSeries.substEquiv_apply (constantCoeff_map_eq_zero _ hH) (isUnit_coeff_one_map _ hl)]

theorem residue_substEquiv_symm (hH : H.constantCoeff = 0) (hl : IsUnit (H.coeff 1))
    (f : CoefficientRing O) :
    residue O ((substEquiv H).symm f) =
      (LaurentSeries.substEquiv (H.map (IsLocalRing.residue O))).symm (residue O f) := by
  rw [substEquiv_symm_apply hH hl, residue_subst, residue_algebraMap_powerSeries,
    LaurentSeries.substEquiv_symm_apply (constantCoeff_map_eq_zero _ hH)
      (isUnit_coeff_one_map _ hl), ← PowerSeries.compInv_eq_substInvOfIsUnit,
    PowerSeries.map_compInv _ hH hl]

end SubstEquiv

end FalseTateNonliftability.CoefficientRing
