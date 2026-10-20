/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Evaluation
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Substitution in Laurent series

Let `R` be a local Artinian ring whose maximal ideal is principal, for instance a field or a
truncation `O ⧸ 𝔪 ^ (r + 1)` of a discrete valuation ring. A Laurent series `G ∈ R((T))` is
admissible if its image in `κ((T))`, where `κ` is the residue field of `R`, has finite positive
order. For admissible `G` there is a unique `R`-algebra endomorphism `f ↦ f(G)` of `R((T))`
that is continuous for the order topology and sends `T` to `G`. It satisfies the chain rule,
composition of substitutions is substitution at the composite, it restricts to substitution of
power series, and it commutes with every ring homomorphism between two such coefficient rings.
A power series `P` with `P(0) = 0` and `P'(0)` a unit gives an automorphism `f ↦ f(P)` of
`R((T))`, whose inverse is substitution at the compositional inverse of `P`; over a field it
preserves the order.

## Main definitions

* `LaurentSeries.IsAdmissible G`: the image of `G` over the residue field has finite positive
  order.
* `LaurentSeries.subst G`: the substitution `f ↦ f(G)`; the identity if `G` is not admissible.
* `LaurentSeries.substEquiv P`: the automorphism `f ↦ f(P)` for a power series `P` with
  `P(0) = 0` and `P'(0)` a unit; the identity for every other `P`.

## Main results

* `LaurentSeries.subst_unique`: `subst G` is the only continuous `R`-algebra endomorphism
  sending `T` to `G`.
* `LaurentSeries.derivative_subst`: the chain rule `f(G)' = f'(G) G'`.
* `LaurentSeries.subst_comp_subst`: `f(G)(H) = f(G(H))`.
* `LaurentSeries.subst_ofPowerSeries`: agreement with `PowerSeries.subst`.
* `LaurentSeries.mapRingHom_subst`: naturality in the coefficient ring.
* `LaurentSeries.isAdmissible_mapRingHom_iff`: admissibility is preserved and reflected by
  every coefficient map.
* `LaurentSeries.substEquiv_symm`: the inverse of `substEquiv P` is `substEquiv` at the
  compositional inverse of `P`.
* `LaurentSeries.order_substEquiv`: over a field, `substEquiv P` preserves the order.
* `LaurentSeries.subst_single_natCard_eq_pow`: over a finite field with `q` elements,
  `f(T ^ q) = f ^ q`.

## Implementation details

For admissible `G` write `G = U + δ Y`, where `δ` generates the maximal ideal of `R` and `U` is
a unit of positive order (`exists_nilpotentLaurentEval_data`); then `nilpotentLaurentEval` at
these data is a substitution of `G` (`exists_subst`). This decomposition is internal to the
proofs: `subst_eq_nilpotentLaurentEval` identifies `subst G` with the evaluation at any such
data, and no other statement refers to it.

## References

* Yuan, Lemma 2.1.
-/

@[expose] public section

namespace LaurentSeries

open scoped LaurentSeries.OrderTopology

noncomputable section

section CommRing

variable {R : Type*} [CommRing R]

private theorem order_eq_of_coeff_ne_zero {f : LaurentSeries R} {m : ℤ} (hm : f.coeff m ≠ 0)
    (hbelow : ∀ j < m, f.coeff j = 0) : f.order = m := by
  have ht := HahnSeries.orderTop_eq_of_le (HahnSeries.mem_support _ _ |>.mpr hm)
    (fun j hj ↦ by
      by_contra h
      exact (HahnSeries.mem_support _ _ |>.mp hj) (hbelow j (lt_of_not_ge h)))
  exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero
    (HahnSeries.ne_zero_of_coeff_ne_zero hm)).trans ht

private theorem order_ofPowerSeries_of_constantCoeff_ne_zero {P : PowerSeries R}
    (hP : P.constantCoeff ≠ 0) : (HahnSeries.ofPowerSeries ℤ R P).order = 0 := by
  apply order_eq_of_coeff_ne_zero
  · simpa only [show (0 : ℤ) = (0 : ℕ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] using hP
  · intro j hj
    rw [PowerSeries.coeff_coe, ite_eq_left hj]

/-- If `H'(0)` is a unit, then the derivative of `H` has order zero. -/
theorem order_derivative_ofPowerSeries [Nontrivial R] {H : PowerSeries R}
    (hlinear : IsUnit (H.coeff 1)) :
    (derivative R (HahnSeries.ofPowerSeries ℤ R H)).order = 0 := by
  rw [derivative_ofPowerSeries]
  apply order_ofPowerSeries_of_constantCoeff_ne_zero
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
    zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using hlinear.ne_zero

private theorem isUnit_coeff_one_substInvOfIsUnit {P : PowerSeries R}
    (hlinear : IsUnit (P.coeff 1)) : IsUnit ((P.substInvOfIsUnit hlinear).coeff 1) := by
  rw [PowerSeries.coeff_one_substInvOfIsUnit]
  exact Units.isUnit _

end CommRing

section IsAdmissible

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]

/-- A Laurent series is admissible if its image over the residue field has finite positive
order. -/
def IsAdmissible (G : LaurentSeries R) : Prop :=
  ∃ a : ℤ, 0 < a ∧ (mapRingHom (IsLocalRing.residue R) G).orderTop = a

/-- Admissibility is finite positive order of the image under any coefficient map whose kernel
is the maximal ideal. -/
theorem isAdmissible_iff_of_ker_eq (φ : R →+* S)
    (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal R) (G : LaurentSeries R) :
    IsAdmissible G ↔ ∃ a : ℤ, 0 < a ∧ (mapRingHom φ G).orderTop = a := by
  rw [IsAdmissible, orderTop_mapRingHom_eq_of_ker_eq (IsLocalRing.residue R) φ
    (IsLocalRing.ker_residue.trans hφ.symm)]

/-- Admissibility is finite positive order modulo a generator of the maximal ideal. -/
theorem isAdmissible_iff_principalReduction {δ : R}
    (hδ : Ideal.span {δ} = IsLocalRing.maximalIdeal R) (G : LaurentSeries R) :
    IsAdmissible G ↔ ∃ a : ℤ, 0 < a ∧ (principalReduction δ G).orderTop = a :=
  isAdmissible_iff_of_ker_eq _ (Ideal.mk_ker.trans hδ) G

/-- A monomial `c T ^ n` with `0 < n` and `c` a unit is admissible. -/
theorem isAdmissible_single {n : ℤ} (hn : 0 < n) {c : R} (hc : IsUnit c) :
    IsAdmissible (HahnSeries.single n c) :=
  ⟨n, hn, by rw [mapRingHom_single, HahnSeries.orderTop_single (hc.map _).ne_zero]⟩

/-- The variable is admissible. -/
theorem isAdmissible_X : IsAdmissible (HahnSeries.single (1 : ℤ) (1 : R)) :=
  isAdmissible_single one_pos isUnit_one

/-- A power series `P` with `P(0) = 0` and `P'(0)` a unit is admissible. -/
theorem isAdmissible_ofPowerSeries {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) : IsAdmissible (HahnSeries.ofPowerSeries ℤ R P) := by
  refine ⟨1, one_pos, le_antisymm ?_ ?_⟩
  · apply HahnSeries.orderTop_le_of_coeff_ne_zero
    rw [mapRingHom_coeff, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff]
    exact (hlinear.map (IsLocalRing.residue R)).ne_zero
  · exact mapRingHom_mem_orderAddSubgroup _ _ _ (ofPowerSeries_mem_orderAddSubgroup_one hP)

/-- The compositional inverse of a power series `P` with `P(0) = 0` and `P'(0)` a unit is
admissible. -/
theorem isAdmissible_ofPowerSeries_substInvOfIsUnit {P : PowerSeries R}
    (hlinear : IsUnit (P.coeff 1)) :
    IsAdmissible (HahnSeries.ofPowerSeries ℤ R (P.substInvOfIsUnit hlinear)) :=
  isAdmissible_ofPowerSeries (PowerSeries.constantCoeff_substInvOfIsUnit P hlinear)
    (isUnit_coeff_one_substInvOfIsUnit hlinear)

end IsAdmissible

section Field

variable {k : Type*} [Field k]

/-- Over a field, a Laurent series is admissible if and only if it has finite positive order. -/
theorem isAdmissible_iff (G : LaurentSeries k) :
    IsAdmissible G ↔ ∃ a : ℤ, 0 < a ∧ G.orderTop = a := by
  rw [IsAdmissible, orderTop_mapRingHom_of_injective _ (IsLocalRing.residue k).injective]

/-- Over a field, a Laurent series is admissible if and only if it is nonzero of positive
order. -/
theorem isAdmissible_iff_ne_zero_and_order_pos (G : LaurentSeries k) :
    IsAdmissible G ↔ G ≠ 0 ∧ 0 < G.order := by
  rw [isAdmissible_iff]
  constructor
  · rintro ⟨a, ha, h⟩
    have hG : G ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨hG, ?_⟩
    rwa [WithTop.coe_inj.mp ((HahnSeries.order_eq_orderTop_of_ne_zero hG).trans h)]
  · rintro ⟨hG, hpos⟩
    exact ⟨G.order, hpos, (HahnSeries.order_eq_orderTop_of_ne_zero hG).symm⟩

end Field

section Artinian

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [CommRing S]

private theorem isNilpotent_of_mem_maximalIdeal {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) : IsNilpotent a := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow ha n
  rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h

private theorem isLocalHom_of_isArtinianRing [Nontrivial S] (φ : R →+* S) : IsLocalHom φ where
  map_nonunit a ha := by
    by_contra h
    exact ((isNilpotent_of_mem_maximalIdeal
      ((IsLocalRing.mem_maximalIdeal a).mpr h)).map φ).not_isUnit ha

variable [IsLocalRing S]

/-- Admissibility is preserved and reflected by every coefficient map. -/
theorem isAdmissible_mapRingHom_iff (φ : R →+* S) (G : LaurentSeries R) :
    IsAdmissible (mapRingHom φ G) ↔ IsAdmissible G := by
  have := isLocalHom_of_isArtinianRing φ
  have hker : RingHom.ker ((IsLocalRing.residue S).comp φ) = IsLocalRing.maximalIdeal R := by
    rw [← RingHom.comap_ker, IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_comap]
  rw [isAdmissible_iff_of_ker_eq _ hker, IsAdmissible, mapRingHom_comp, RingHom.comp_apply]

/-- The image of an admissible series under a coefficient map is admissible. -/
theorem IsAdmissible.map {G : LaurentSeries R} (hG : IsAdmissible G) (φ : R →+* S) :
    IsAdmissible (mapRingHom φ G) :=
  (isAdmissible_mapRingHom_iff φ G).mpr hG

end Artinian

section Subst

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]
  [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsPrincipalIdealRing S]

private theorem exists_eq_add_C_mul {G : LaurentSeries R} (hG : IsAdmissible G) :
    ∃ (δ : R) (U Y : LaurentSeries R) (r : ℕ) (a c : ℤ), 1 ≤ r ∧ δ ^ r = 0 ∧ 0 < a ∧ 0 ≤ c ∧
      (a : WithTop ℤ) ≤ U.orderTop ∧ ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop ∧ IsUnit U ∧
      G = U + HahnSeries.C δ * Y := by
  obtain ⟨δ, hspan⟩ : ∃ δ : R, Ideal.span {δ} = IsLocalRing.maximalIdeal R :=
    ⟨_, Ideal.span_singleton_generator _⟩
  have : (Ideal.span {δ}).IsMaximal := by
    rw [hspan]
    exact IsLocalRing.maximalIdeal.isMaximal R
  obtain ⟨n, hn⟩ := isNilpotent_of_mem_maximalIdeal (show δ ∈ IsLocalRing.maximalIdeal R by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self δ)
  have hpow : δ ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  obtain ⟨a, ha, horder⟩ := (isAdmissible_iff_principalReduction hspan G).mp hG
  obtain ⟨U, Y, c, -, hdecomp, hUorder, hUunit, hc, hY⟩ :=
    exists_nilpotentLaurentEval_data δ G (n + 1) hpow a horder
  exact ⟨δ, U, Y, n + 1, a, c, by omega, hpow, ha, hc, hUorder.ge, hY, hUunit, hdecomp⟩

/-- An admissible series is the image of the variable under a continuous `R`-algebra
endomorphism satisfying the chain rule. -/
theorem exists_subst {G : LaurentSeries R} (hG : IsAdmissible G) :
    ∃ F : LaurentSeries R →ₐ[R] LaurentSeries R,
      Continuous F ∧
        F (HahnSeries.single (1 : ℤ) (1 : R)) = G ∧
        ∀ f, derivative R (F f) = F (derivative R f) * derivative R G := by
  obtain ⟨δ, U, Y, r, a, c, hr, hδ, ha, hc, hU, hY, hUunit, rfl⟩ := exists_eq_add_C_mul hG
  exact ⟨_, continuous_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit,
    nilpotentLaurentEval_X δ U Y r hr hδ a c ha hc hU hY hUunit,
    derivative_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit⟩

open scoped Classical in
/-- Substitution of `G` for the variable: for admissible `G`, the continuous `R`-algebra
endomorphism `f ↦ f(G)` of `R((T))` (see `subst_unique`); the identity otherwise. -/
def subst (G : LaurentSeries R) : LaurentSeries R →ₐ[R] LaurentSeries R :=
  if hG : IsAdmissible G then Classical.choose (exists_subst hG) else AlgHom.id R _

private theorem subst_spec {G : LaurentSeries R} (hG : IsAdmissible G) :
    Continuous (subst G) ∧
      subst G (HahnSeries.single (1 : ℤ) (1 : R)) = G ∧
      ∀ f, derivative R (subst G f) = subst G (derivative R f) * derivative R G := by
  have h : subst G = Classical.choose (exists_subst hG) := dite_eq_left hG
  rw [h]
  exact Classical.choose_spec (exists_subst hG)

theorem subst_of_not_isAdmissible {G : LaurentSeries R} (hG : ¬ IsAdmissible G) :
    subst G = AlgHom.id R _ :=
  dite_eq_right hG

/-- Substitution is continuous for the order topology. -/
theorem continuous_subst (G : LaurentSeries R) : Continuous (subst G) := by
  by_cases hG : IsAdmissible G
  · exact (subst_spec hG).1
  · rw [subst_of_not_isAdmissible hG, AlgHom.coe_id]
    exact continuous_id

@[simp]
theorem subst_X {G : LaurentSeries R} (hG : IsAdmissible G) :
    subst G (HahnSeries.single (1 : ℤ) (1 : R)) = G :=
  (subst_spec hG).2.1

@[simp]
theorem subst_C (G : LaurentSeries R) (b : R) : subst G (HahnSeries.C b) = HahnSeries.C b := by
  simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    HahnSeries.ofPowerSeries_C] using (subst G).commutes b

/-- The chain rule `f(G)' = f'(G) G'`. -/
theorem derivative_subst {G : LaurentSeries R} (hG : IsAdmissible G) (f : LaurentSeries R) :
    derivative R (subst G f) = subst G (derivative R f) * derivative R G :=
  (subst_spec hG).2.2 f

/-- A continuous `R`-algebra endomorphism sending the variable to an admissible `G` is the
substitution of `G`. -/
theorem subst_unique {G : LaurentSeries R} (hG : IsAdmissible G)
    (F : LaurentSeries R →ₐ[R] LaurentSeries R)
    (hF : Continuous F) (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) = G) : F = subst G :=
  continuous_algHom_ext_X F (subst G) hF (continuous_subst G) (hX.trans (subst_X hG).symm)

/-- Substitution of the variable is the identity. -/
theorem subst_X_left : subst (HahnSeries.single (1 : ℤ) (1 : R)) = AlgHom.id R _ :=
  (subst_unique isAdmissible_X _ continuous_id rfl).symm

@[simp]
theorem subst_X_left_apply (f : LaurentSeries R) :
    subst (HahnSeries.single (1 : ℤ) (1 : R)) f = f := by
  rw [subst_X_left, AlgHom.id_apply]

/-- An admissible series is a unit. -/
theorem IsAdmissible.isUnit {G : LaurentSeries R} (hG : IsAdmissible G) : IsUnit G := by
  have hX : IsUnit (HahnSeries.single (1 : ℤ) (1 : R) : LaurentSeries R) :=
    IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : R)) (by simp)
  simpa only [subst_X hG] using hX.map (LaurentSeries.subst G)

/-- Substitution of `G = U + ε Y`, with `ε` nilpotent and `U` a unit of positive order, is the
evaluation `nilpotentLaurentEval` at these data. -/
theorem subst_eq_nilpotentLaurentEval {G : LaurentSeries R} (hG : IsAdmissible G)
    (ε : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hpow : ε ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c) (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)
    (hdecomp : G = U + HahnSeries.C ε * Y) :
    subst G = nilpotentLaurentEval ε U Y r hr hpow a c ha hc hU hY hUunit :=
  (subst_unique hG _ (continuous_nilpotentLaurentEval ε U Y r hr hpow a c ha hc hU hY hUunit)
    ((nilpotentLaurentEval_X ε U Y r hr hpow a c ha hc hU hY hUunit).trans hdecomp.symm)).symm

/-- Substitution commutes with coefficient maps: `φ(f(G)) = (φ f)(φ G)` for every `G`. -/
theorem mapRingHom_subst (φ : R →+* S) (G f : LaurentSeries R) :
    mapRingHom φ (subst G f) = subst (mapRingHom φ G) (mapRingHom φ f) := by
  by_cases hG : IsAdmissible G
  swap
  · rw [subst_of_not_isAdmissible hG,
      subst_of_not_isAdmissible (mt (isAdmissible_mapRingHom_iff φ G).mp hG), AlgHom.id_apply,
      AlgHom.id_apply]
  obtain ⟨δ, U, Y, r, a, c, hr, hδ, ha, hc, hU, hY, hUunit, hdecomp⟩ := exists_eq_add_C_mul hG
  rw [subst_eq_nilpotentLaurentEval hG δ U Y r hr hδ a c ha hc hU hY hUunit hdecomp,
    subst_eq_nilpotentLaurentEval (hG.map φ) (φ δ) (mapRingHom φ U) (mapRingHom φ Y) r hr
      (by rw [← map_pow, hδ, map_zero]) a c ha hc (hU.trans (orderTop_le_mapRingHom φ U))
      (hY.trans (orderTop_le_mapRingHom φ Y)) (hUunit.map _)
      (by rw [hdecomp, map_add, map_mul, mapRingHom_C])]
  exact mapRingHom_nilpotentLaurentEval φ δ U Y r hr hδ a c ha hc hU hY hUunit f

theorem semiconj_mapRingHom_subst (φ : R →+* S) (G : LaurentSeries R) :
    Function.Semiconj (mapRingHom φ) (subst G) (subst (mapRingHom φ G)) :=
  mapRingHom_subst φ G

theorem mapRingHom_subst_iterate (φ : R →+* S) (G : LaurentSeries R) (n : ℕ)
    (f : LaurentSeries R) :
    mapRingHom φ ((subst G)^[n] f) = (subst (mapRingHom φ G))^[n] (mapRingHom φ f) :=
  (semiconj_mapRingHom_subst φ G).iterate_right n f

/-- Over a field, substitution of an admissible `G` multiplies a nonnegative lower bound on the
order by the order of `G`. -/
theorem subst_mem_orderAddSubgroup {k : Type*} [Field k] {G : LaurentSeries k}
    (hG : IsAdmissible G) (N : ℕ) {f : LaurentSeries k} (hf : f ∈ orderAddSubgroup (N : ℤ)) :
    subst G f ∈ orderAddSubgroup (G.order * N) := by
  obtain ⟨hG0, hpos⟩ := (isAdmissible_iff_ne_zero_and_order_pos G).mp hG
  have hGorder : (G.order : WithTop ℤ) ≤ G.orderTop :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hG0).le
  rw [subst_eq_nilpotentLaurentEval hG 0 G 0 1 le_rfl (pow_one 0) G.order 0 hpos le_rfl hGorder
    (by simp) hG.isUnit (by simp)]
  simpa only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero] using
    nilpotentLaurentEval_mem_orderAddSubgroup 0 G 0 1 le_rfl (pow_one 0) G.order 0 hpos le_rfl
      hGorder (by simp) hG.isUnit N f hf

private theorem isAdmissible_subst_of_field {k : Type*} [Field k] {G H : LaurentSeries k}
    (hG : IsAdmissible G) (hH : IsAdmissible H) : IsAdmissible (subst H G) := by
  obtain ⟨-, hGpos⟩ := (isAdmissible_iff_ne_zero_and_order_pos G).mp hG
  obtain ⟨-, hHpos⟩ := (isAdmissible_iff_ne_zero_and_order_pos H).mp hH
  have hne : subst H G ≠ 0 := (hG.isUnit.map (subst H)).ne_zero
  have hG1 : G ∈ orderAddSubgroup ((1 : ℕ) : ℤ) :=
    orderAddSubgroup_antitone (show ((1 : ℕ) : ℤ) ≤ G.order by omega)
      (mem_orderAddSubgroup_order G)
  have hbound := subst_mem_orderAddSubgroup hH 1 hG1
  rw [Nat.cast_one, mul_one, mem_orderAddSubgroup,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hne, WithTop.coe_le_coe] at hbound
  exact (isAdmissible_iff_ne_zero_and_order_pos _).mpr ⟨hne, hHpos.trans_le hbound⟩

/-- If `G` and `H` are admissible, so is `G(H)`. -/
theorem IsAdmissible.subst {G H : LaurentSeries R} (hG : IsAdmissible G)
    (hH : IsAdmissible H) : IsAdmissible (LaurentSeries.subst H G) := by
  rw [← isAdmissible_mapRingHom_iff (IsLocalRing.residue R),
    mapRingHom_subst (IsLocalRing.residue R) H]
  exact isAdmissible_subst_of_field (hG.map _) (hH.map _)

/-- Composition of substitutions: `f(G)(H) = f(G(H))`. -/
theorem subst_comp_subst {G H : LaurentSeries R} (hG : IsAdmissible G) (hH : IsAdmissible H) :
    (subst H).comp (subst G) = subst (subst H G) :=
  subst_unique (hG.subst hH) _ ((continuous_subst H).comp (continuous_subst G))
    (by rw [AlgHom.comp_apply, subst_X hG])

theorem subst_comp_subst_apply {G H : LaurentSeries R} (hG : IsAdmissible G)
    (hH : IsAdmissible H) (f : LaurentSeries R) :
    subst H (subst G f) = subst (subst H G) f :=
  AlgHom.congr_fun (subst_comp_subst hG hH) f

/-- Substitutions of `G` and `H` commute if `H(G) = G(H)`. -/
theorem subst_commute {G H : LaurentSeries R} (hG : IsAdmissible G) (hH : IsAdmissible H)
    (h : subst G H = subst H G) : Function.Commute (subst G) (subst H) := fun f ↦ by
  rw [subst_comp_subst_apply hH hG, subst_comp_subst_apply hG hH, h]

/-- The iterates `G^{∘ n}` of an admissible `G` are admissible. -/
theorem IsAdmissible.iterate {G : LaurentSeries R} (hG : IsAdmissible G) (n : ℕ) :
    IsAdmissible ((LaurentSeries.subst G)^[n] (HahnSeries.single (1 : ℤ) (1 : R))) := by
  induction n with
  | zero => exact isAdmissible_X
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.subst hG

/-- Substitution of the iterate `G^{∘ n}` is the `n`-th iterate of substitution of `G`. -/
theorem subst_iterate {G : LaurentSeries R} (hG : IsAdmissible G) (n : ℕ)
    (f : LaurentSeries R) :
    subst ((subst G)^[n] (HahnSeries.single (1 : ℤ) (1 : R))) f = (subst G)^[n] f := by
  induction n generalizing f with
  | zero => exact subst_X_left_apply f
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← subst_comp_subst_apply (hG.iterate n) hG, ih,
      Function.iterate_succ_apply']

/-- On power series, substitution of a power series `P` with `P(0) = 0` is
`PowerSeries.subst`. -/
theorem subst_ofPowerSeries {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hG : IsAdmissible (HahnSeries.ofPowerSeries ℤ R P)) (f : PowerSeries R) :
    subst (HahnSeries.ofPowerSeries ℤ R P) (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (f.subst P) := by
  have hbound : (1 : WithTop ℤ) ≤ (HahnSeries.ofPowerSeries ℤ R P).orderTop :=
    ofPowerSeries_mem_orderAddSubgroup_one hP
  rw [subst_eq_nilpotentLaurentEval hG 0 (HahnSeries.ofPowerSeries ℤ R P) 0 1
    (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) hG.isUnit (by simp),
    nilpotentLaurentEval_ofPowerSeries]
  ext j
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, nilpotentPowerSeriesEval_coeff,
      HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hP)]
    apply finsum_congr
    intro d
    simp only [map_zero, zero_mul, add_zero,
      ← map_pow (HahnSeries.ofPowerSeries ℤ R), HahnSeries.ofPowerSeries_apply_coeff]
  | negSucc n =>
    have hz : nilpotentPowerSeriesEval 0 (HahnSeries.ofPowerSeries ℤ R P) 0 1
        (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) f ∈ orderAddSubgroup 0 := by
      simpa only [Nat.cast_zero, mul_zero, Nat.sub_self, zero_mul, sub_zero] using
        nilpotentPowerSeriesEval_mem_orderAddSubgroup 0 (HahnSeries.ofPowerSeries ℤ R P) 0 1
          (by omega) (by simp) 1 0 (by omega) le_rfl hbound (by simp) 0 f (by intro n hn; omega)
    rw [(mem_orderAddSubgroup_iff_coeff _ _).mp hz (Int.negSucc n) (by omega),
      PowerSeries.coeff_coe, ite_eq_left (Int.negSucc_lt_zero n)]

/-- If `Q(P) = T`, then substitution of `Q` followed by substitution of `P` is the identity. -/
theorem subst_ofPowerSeries_comp_eq_id {P Q : PowerSeries R} (hP : P.constantCoeff = 0)
    (hPadm : IsAdmissible (HahnSeries.ofPowerSeries ℤ R P))
    (hQadm : IsAdmissible (HahnSeries.ofPowerSeries ℤ R Q)) (hQP : Q.subst P = PowerSeries.X) :
    (subst (HahnSeries.ofPowerSeries ℤ R P)).comp (subst (HahnSeries.ofPowerSeries ℤ R Q)) =
      AlgHom.id R (LaurentSeries R) := by
  rw [subst_comp_subst hQadm hPadm, subst_ofPowerSeries hP hPadm, hQP, HahnSeries.ofPowerSeries_X,
    subst_X_left]

open scoped Classical in
/-- The automorphism `f ↦ f(P)` of `R((T))` for a power series `P` with `P(0) = 0` and `P'(0)` a
unit; its inverse is `f ↦ f(Q)` for the compositional inverse `Q` of `P`. For every other `P`
this is the identity. -/
def substEquiv (P : PowerSeries R) : LaurentSeries R ≃ₐ[R] LaurentSeries R :=
  if h : P.constantCoeff = 0 ∧ IsUnit (P.coeff 1) then
    AlgEquiv.ofAlgHom (subst (HahnSeries.ofPowerSeries ℤ R P))
      (subst (HahnSeries.ofPowerSeries ℤ R (P.substInvOfIsUnit h.2)))
      (subst_ofPowerSeries_comp_eq_id h.1 (isAdmissible_ofPowerSeries h.1 h.2)
        (isAdmissible_ofPowerSeries_substInvOfIsUnit h.2)
        (PowerSeries.subst_substInvOfIsUnit_left P h.1 h.2))
      (subst_ofPowerSeries_comp_eq_id (PowerSeries.constantCoeff_substInvOfIsUnit P h.2)
        (isAdmissible_ofPowerSeries_substInvOfIsUnit h.2) (isAdmissible_ofPowerSeries h.1 h.2)
        (PowerSeries.subst_substInvOfIsUnit_right P h.1 h.2))
  else AlgEquiv.refl

theorem substEquiv_of_not {P : PowerSeries R}
    (h : ¬ (P.constantCoeff = 0 ∧ IsUnit (P.coeff 1))) : substEquiv P = AlgEquiv.refl :=
  dite_eq_right h

theorem substEquiv_apply {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : LaurentSeries R) :
    substEquiv P f = subst (HahnSeries.ofPowerSeries ℤ R P) f := by
  rw [substEquiv, dite_eq_left ⟨hP, hlinear⟩]
  rfl

theorem substEquiv_symm_apply {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : LaurentSeries R) :
    (substEquiv P).symm f =
      subst (HahnSeries.ofPowerSeries ℤ R (P.substInvOfIsUnit hlinear)) f := by
  rw [substEquiv, dite_eq_left ⟨hP, hlinear⟩]
  rfl

/-- The inverse of `substEquiv P` is `substEquiv` at the compositional inverse of `P`. -/
theorem substEquiv_symm {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) :
    (substEquiv P).symm = substEquiv (P.substInvOfIsUnit hlinear) :=
  AlgEquiv.ext fun f ↦ by
    rw [substEquiv_symm_apply hP hlinear,
      substEquiv_apply (PowerSeries.constantCoeff_substInvOfIsUnit P hlinear)
        (isUnit_coeff_one_substInvOfIsUnit hlinear)]

theorem substEquiv_X {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) :
    substEquiv P (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.ofPowerSeries ℤ R P := by
  rw [substEquiv_apply hP hlinear, subst_X (isAdmissible_ofPowerSeries hP hlinear)]

theorem substEquiv_ofPowerSeries {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : PowerSeries R) :
    substEquiv P (HahnSeries.ofPowerSeries ℤ R f) = HahnSeries.ofPowerSeries ℤ R (f.subst P) := by
  rw [substEquiv_apply hP hlinear, subst_ofPowerSeries hP (isAdmissible_ofPowerSeries hP hlinear)]

/-- The chain rule for `substEquiv P`. -/
theorem derivative_substEquiv {P : PowerSeries R} (hP : P.constantCoeff = 0)
    (hlinear : IsUnit (P.coeff 1)) (f : LaurentSeries R) :
    derivative R (substEquiv P f) =
      substEquiv P (derivative R f) * derivative R (HahnSeries.ofPowerSeries ℤ R P) := by
  rw [substEquiv_apply hP hlinear, substEquiv_apply hP hlinear,
    derivative_subst (isAdmissible_ofPowerSeries hP hlinear)]

theorem continuous_substEquiv (P : PowerSeries R) : Continuous (substEquiv P) := by
  by_cases h : P.constantCoeff = 0 ∧ IsUnit (P.coeff 1)
  · rw [show ⇑(substEquiv P) = subst (HahnSeries.ofPowerSeries ℤ R P) from
      funext (substEquiv_apply h.1 h.2)]
    exact continuous_subst _
  · rw [substEquiv_of_not h, AlgEquiv.coe_refl]
    exact continuous_id

theorem continuous_substEquiv_symm (P : PowerSeries R) : Continuous (substEquiv P).symm := by
  by_cases h : P.constantCoeff = 0 ∧ IsUnit (P.coeff 1)
  · rw [substEquiv_symm h.1 h.2]
    exact continuous_substEquiv _
  · rw [substEquiv_of_not h, AlgEquiv.refl_symm, AlgEquiv.coe_refl]
    exact continuous_id

/-- Composition of power-series coordinates: `f ↦ f(Q(P))` is `f ↦ f(Q)` followed by
`f ↦ f(P)`. -/
theorem substEquiv_subst {P Q : PowerSeries R} (hP : P.constantCoeff = 0)
    (hPlinear : IsUnit (P.coeff 1)) (hQ : Q.constantCoeff = 0)
    (hQlinear : IsUnit (Q.coeff 1)) :
    substEquiv (Q.subst P) = (substEquiv Q).trans (substEquiv P) := by
  have h0 : PowerSeries.constantCoeff (Q.subst P) = 0 := by
    simpa only [PowerSeries.constantCoeff_eq] using
      PowerSeries.constantCoeff_subst_eq_zero hP Q hQ
  have h1 : IsUnit (PowerSeries.coeff 1 (Q.subst P)) := by
    rw [PowerSeries.coeff_one_subst hP]
    exact hQlinear.mul hPlinear
  refine AlgEquiv.ext fun f ↦ ?_
  rw [AlgEquiv.trans_apply, substEquiv_apply h0 h1, substEquiv_apply hQ hQlinear,
    substEquiv_apply hP hPlinear,
    subst_comp_subst_apply (isAdmissible_ofPowerSeries hQ hQlinear)
      (isAdmissible_ofPowerSeries hP hPlinear),
    subst_ofPowerSeries hP (isAdmissible_ofPowerSeries hP hPlinear)]

section Field

variable {k : Type*} [Field k]

/-- Over a field, `substEquiv H` preserves the order of every Laurent series. -/
theorem order_substEquiv {H : PowerSeries k} (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) (f : LaurentSeries k) :
    (substEquiv H f).order = f.order := by
  let E := substEquiv H
  have hEne (m : ℤ) : E (HahnSeries.single m 1) ≠ 0 := by
    intro h
    apply HahnSeries.single_ne_zero (a := m) (one_ne_zero : (1 : k) ≠ 0)
    apply E.injective
    simpa only [map_zero] using h
  have hHorder : (HahnSeries.ofPowerSeries ℤ k H).order = 1 := by
    apply order_eq_of_coeff_ne_zero
    · simpa only [show (1 : ℤ) = (1 : ℕ) from rfl,
        HahnSeries.ofPowerSeries_apply_coeff] using hlinear.ne_zero
    · intro j hj
      rw [PowerSeries.coeff_coe]
      by_cases hj0 : j < 0
      · rw [ite_eq_left hj0]
      · have hjz : j = 0 := by omega
        subst j
        simpa only [lt_self_iff_false, ite_false, Int.natAbs_zero,
          PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero
  have hX : E (HahnSeries.single (1 : ℤ) 1) = HahnSeries.ofPowerSeries ℤ k H :=
    substEquiv_X hzero hlinear
  have hn (n : ℕ) : (E (HahnSeries.single (n : ℤ) 1)).order = n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hm : (HahnSeries.single ((n + 1 : ℕ) : ℤ) 1 : LaurentSeries k) =
          HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 := by
        simp [HahnSeries.single_mul_single]
      rw [hm, map_mul, HahnSeries.order_mul (hEne _) (hEne _), ih, hX, hHorder]
      simp only [Nat.cast_add, Nat.cast_one]
  have hz (m : ℤ) : (E (HahnSeries.single m 1)).order = m := by
    cases m with
    | ofNat n => exact hn n
    | negSucc n =>
      have hm : (Int.negSucc n : ℤ) + ((n + 1 : ℕ) : ℤ) = 0 := by omega
      have hprod : E (HahnSeries.single (Int.negSucc n) 1) *
          E (HahnSeries.single ((n + 1 : ℕ) : ℤ) 1) = 1 := by
        rw [← map_mul, HahnSeries.single_mul_single, hm, one_mul]
        simp
      have ho := congrArg HahnSeries.order hprod
      rw [HahnSeries.order_mul (hEne _) (hEne _), hn, HahnSeries.order_one] at ho
      omega
  by_cases hf : f = 0
  · subst f
    simp
  have hpart : f.powerSeriesPart.constantCoeff ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff,
      Nat.cast_zero, add_zero] using (HahnSeries.coeff_order_eq_zero.not.mpr hf)
  have hsubst : PowerSeries.constantCoeff (f.powerSeriesPart.subst H) =
      f.powerSeriesPart.constantCoeff := by
    simpa only [PowerSeries.constantCoeff_eq, Algebra.algebraMap_self_apply] using
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hzero f.powerSeriesPart
  have hpartOrder : (E (HahnSeries.ofPowerSeries ℤ k f.powerSeriesPart)).order = 0 := by
    rw [substEquiv_ofPowerSeries hzero hlinear]
    exact order_ofPowerSeries_of_constantCoeff_ne_zero (by rwa [hsubst])
  have hpartUnit : IsUnit (E (HahnSeries.ofPowerSeries ℤ k f.powerSeriesPart)) :=
    ((PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hpart)).map
      (HahnSeries.ofPowerSeries ℤ k)).map E
  have heq : E f = E (HahnSeries.single f.order 1) *
      E (HahnSeries.ofPowerSeries ℤ k f.powerSeriesPart) :=
    (congrArg E (single_order_mul_powerSeriesPart f)).symm.trans (map_mul E _ _)
  rw [heq, HahnSeries.order_mul (hEne _) hpartUnit.ne_zero, hz, hpartOrder, add_zero]

/-- Over a field, `substEquiv H` preserves `orderTop`. -/
theorem orderTop_substEquiv {H : PowerSeries k} (hzero : H.constantCoeff = 0)
    (hlinear : IsUnit (H.coeff 1)) (f : LaurentSeries k) :
    (substEquiv H f).orderTop = f.orderTop := by
  by_cases hf : f = 0
  · rw [hf, map_zero]
  have hEf : substEquiv H f ≠ 0 := (map_ne_zero_iff _ (substEquiv H).injective).mpr hf
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hEf, order_substEquiv hzero hlinear,
    HahnSeries.order_eq_orderTop_of_ne_zero hf]

/-- Over a finite field with `q` elements, substitution of `T ^ q` is the Frobenius `f ↦ f ^ q`. -/
theorem subst_single_natCard_eq_pow [Finite k] (f : LaurentSeries k) :
    subst (HahnSeries.single (Nat.card k : ℤ) 1) f = f ^ Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  have hF := subst_unique (isAdmissible_single (Nat.cast_pos.mpr Nat.card_pos) isUnit_one)
    (FiniteField.frobeniusAlgHom k (LaurentSeries k))
    (by rw [FiniteField.coe_frobeniusAlgHom]; exact continuous_pow _)
    (by rw [FiniteField.frobeniusAlgHom_apply, HahnSeries.single_pow, one_pow, nsmul_one,
      Nat.card_eq_fintype_card (α := k)])
  rw [← hF, FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card (α := k)]

end Field

end Subst

end

end LaurentSeries
