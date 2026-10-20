/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.NormalForm
public import FalseTateNonliftability.PowerSeries.PrincipalUnitPowers
public import FalseTateNonliftability.Liftability.CoordinateChange
public import FalseTateNonliftability.Liftability.FieldOfNorms
public import FalseTateExtension.Padic.Basic

/-!
# `F`-liftability of the action on the field of norms

Let `K` be a finite extension of `ℚ_p`, let `L/K` be an infinite totally ramified APF extension
inside an algebraic closure `K^alg`, and let `F ⊆ K^alg` be a finite extension of `ℚ_p` with the
same residue field as `K`. Let `κ_F` be the residue field of the ring of integers `𝒪_F` of `F` and
let `A_K` be the `𝔪_F`-adic completion of `𝒪_F((T))`. As `L/K` is totally ramified, the residue
field `κ_L` of the field of norms `X_K(L)` is the residue field of `K`, hence isomorphic to `κ_F`.
For a uniformizer `u` of `X_K(L)`, the coordinate series `f_{g,u}` of the elements
`g ∈ Aut(L/K)` (`ev_u(f_{g,u}) = g(u)`, Yuan, §1.4) thus form a coordinate family over `κ_F`. The
action of `Aut(L/K)` on `X_K(L)` is `F`-liftable if this family has a lift to `A_K` (Berger 2014;
Yuan, Definition 1.1): there exist `P` and `(F_g)_{g ∈ Aut(L/K)}` in `A_K` with `P̄ = T^q`,
`ev_u(F̄_g) = g(u)`, `F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}`.

A change of uniformizer conjugates the coordinate family by a change of variable
(Yuan, Lemma 2.2 (4)), so `F`-liftability does not depend on the uniformizer, and neither does the
existence of finite lifts modulo `𝔪_F ^ (r + 1)` on a subset of `Aut(L/K)`
(Yuan, Proposition 2.3).

For `K = ℚ_p` the condition on `F` is that `F/ℚ_p` is totally ramified; then `κ_F` has `p`
elements.

## Main definitions

* `FalseTateNonliftability.baseField p K`: the image of `K` in `K^alg`, an intermediate field of
  `K^alg/ℚ_p`. "`F` has the same residue field as `K`" is `(baseField p K).HasSameResidueField F`.
* `FalseTateNonliftability.IsLiftable.residueFieldEquiv p K L F`: the isomorphism `κ_L ≅ κ_F`.
* `FalseTateNonliftability.IsLiftable.coordinateFamily p K L F u hu`: the coordinate family
  `(f_{g,u})_{g ∈ Aut(L/K)}` over `κ_F`.
* `FalseTateNonliftability.IsLiftable p K L F`: the action of `Aut(L/K)` on `X_K(L)` is
  `F`-liftable.

## Main results

* `FalseTateNonliftability.isLiftable_iff_uniformizer`,
  `FalseTateNonliftability.isLiftable_iff_exists_uniformizer`,
  `FalseTateNonliftability.isLiftable_iff_forall_uniformizer`,
  `FalseTateNonliftability.IsLiftable.liftable_coordinateFamily_iff`,
  `FalseTateNonliftability.IsLiftable.finiteLiftable_coordinateFamily_iff`: Yuan,
  Proposition 2.3.
* `FalseTateNonliftability.hasSameResidueField_baseField_padic`: a totally ramified extension of
  `ℚ_p` has the same residue field as `ℚ_p`.
* `FalseTateNonliftability.fact_natCard_residueField_spectralIntegerRing`: the residue field of a
  finite totally ramified extension of `ℚ_p` has `p` elements.
* `FalseTateNonliftability.IsLiftable.order_coordinateFamily_series_sub_X`,
  `FalseTateNonliftability.IsLiftable.ramificationNumber_coordinateFamily_series`,
  `FalseTateNonliftability.IsLiftable.orderOf_coeff_one_coordinateFamily_series`,
  `FalseTateNonliftability.IsLiftable.isOfFinOrder_substEquiv_coordinateFamily_series_iff`: the
  isomorphism `κ_L ≅ κ_F` preserves the orders of `f_{g,u} - T`, the ramification numbers, the
  orders of the linear coefficients and the orders of the automorphisms `a ↦ a ∘ f_{g,u}`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  §1.4, Definition 1.1, Lemma 2.2 and Proposition 2.3.
* Berger 2014, Definition 1.1 in Yuan.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger PowerSeries
open IsLocalRing (ResidueField)
open scoped PowerSeries

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An injective coefficient map preserves ramification numbers. -/
theorem ramificationNumber_map {φ : R →+* S} (hφ : Function.Injective φ) (f : R⟦X⟧) :
    (f.map φ).ramificationNumber = f.ramificationNumber := by
  have key (A : LaurentSeries R) : (LaurentSeries.mapRingHom φ A).order = A.order := by
    by_cases hA : A = 0
    · rw [hA, map_zero, HahnSeries.order_zero, HahnSeries.order_zero]
    have ht := LaurentSeries.orderTop_mapRingHom_of_injective φ hφ A
    have hA' : LaurentSeries.mapRingHom φ A ≠ 0 := by
      rw [← HahnSeries.orderTop_ne_top, ht, HahnSeries.orderTop_ne_top]
      exact hA
    exact WithTop.coe_inj.mp ((HahnSeries.order_eq_orderTop_of_ne_zero hA').trans
      (ht.trans (HahnSeries.order_eq_orderTop_of_ne_zero hA).symm))
  rw [ramificationNumber, ramificationNumber, ← key, map_sub,
    LaurentSeries.mapRingHom_ofPowerSeries, LaurentSeries.mapRingHom_single, φ.map_one]

/-- If `f - T` has order `n`, then the ramification number of `f` is `n - 1`. -/
theorem ramificationNumber_eq_of_order_sub_X_eq {f : R⟦X⟧} {n : ℕ}
    (h : (f - X).order = (n : ℕ∞)) : f.ramificationNumber = n - 1 := by
  have hf : f ≠ X := by
    rintro rfl
    simp at h
  have ht := orderTop_ofPowerSeries_sub_X hf
  rw [← HahnSeries.ofPowerSeries_X, ← map_sub, HahnSeries.orderTop_ofPowerSeries] at ht
  have h' : ((n : ℤ) : WithTop ℤ) = ((f.ramificationNumber + 1 : ℤ) : WithTop ℤ) :=
    (congrArg (WithTop.map fun n : ℕ ↦ (n : ℤ)) h).symm.trans ht
  rw [WithTop.coe_inj] at h'
  omega

end PowerSeries

namespace FalseTateNonliftability

namespace CoordinateFamily

open LaurentSeries

variable {κ κ' : Type*} [CommRing κ] [IsLocalRing κ] [IsArtinianRing κ] [IsPrincipalIdealRing κ]
  [CommRing κ'] [IsLocalRing κ'] [IsArtinianRing κ'] [IsPrincipalIdealRing κ']
  {Γ : Type*} [Monoid Γ] (f : CoordinateFamily κ Γ)

/-- The substitution `a ↦ a ∘ P` is the identity exactly for `P = T`. -/
private theorem substEquiv_eq_one_iff {P : PowerSeries κ} (hP : P.constantCoeff = 0)
    (hP' : IsUnit (P.coeff 1)) : substEquiv P = 1 ↔ P = X := by
  constructor
  · intro h
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [← substEquiv_X hP hP', h, HahnSeries.ofPowerSeries_X]
    rfl
  · rintro rfl
    refine AlgEquiv.ext fun a ↦ ?_
    rw [substEquiv_apply constantCoeff_X (by simp), HahnSeries.ofPowerSeries_X,
      subst_X_left_apply]
    rfl

/-- The automorphism `a ↦ a ∘ f_g` of `κ((T))` has finite order if and only if `f_{g ^ n} = T` for
some `n > 0`. -/
theorem isOfFinOrder_substEquiv_series_iff (g : Γ) :
    IsOfFinOrder (substEquiv (f.series g)) ↔ ∃ n, 0 < n ∧ f.series (g ^ n) = X := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  have h0 := f.constantCoeff_series (g ^ n)
  have h1 := f.isUnit_coeff_one_series (g ^ n)
  rw [← substEquiv_eq_one_iff h0 h1, f.series_pow, substEquiv_iterate (f.constantCoeff_series g)
    (f.isUnit_coeff_one_series g)]

/-- An injective coefficient map preserves the orders of the automorphisms `a ↦ a ∘ f_g`. -/
theorem isOfFinOrder_substEquiv_map_series_iff {φ : κ →+* κ'} (hφ : Function.Injective φ)
    (g : Γ) :
    IsOfFinOrder (substEquiv ((f.map φ).series g)) ↔ IsOfFinOrder (substEquiv (f.series g)) := by
  rw [isOfFinOrder_substEquiv_series_iff, isOfFinOrder_substEquiv_series_iff]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  rw [map_series, ← map_X φ]
  exact (map_injective φ hφ).eq_iff

end CoordinateFamily

namespace FieldOfNorms

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]
  [Fact (¬ Module.Finite K L)] [IsTotallyRamified K L]
  {u : FieldOfNorms K L} (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ))

/-- The automorphism `a ↦ a ∘ f_{g,u}` of `κ_L((T))` has finite order if and only if
`f_{g ^ n, u} = T` for some `n > 0`. -/
theorem isOfFinOrder_substEquiv_coordinateSeries_iff (g : L ≃ₐ[K] L) :
    IsOfFinOrder (LaurentSeries.substEquiv (coordinateSeries K L u hu g)) ↔
      ∃ n, 0 < n ∧ coordinateSeries K L u hu (g ^ n) = X :=
  (coordinateFamily K L u hu).isOfFinOrder_substEquiv_series_iff g

end FieldOfNorms

section BaseField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K]

/-- The image of `K` in its algebraic closure `K^alg`, as an intermediate field of `K^alg/ℚ_p`. -/
def baseField : IntermediateField ℚ_[p] (AlgebraicClosure K) :=
  (IsScalarTower.toAlgHom ℚ_[p] K (AlgebraicClosure K)).fieldRange

/-- `K` is isomorphic over `ℚ_p` to its image in `K^alg`. -/
def baseFieldEquiv : K ≃ₐ[ℚ_[p]] baseField p K :=
  (IsScalarTower.toAlgHom ℚ_[p] K (AlgebraicClosure K)).equivFieldRange

/-- The image of `ℚ_p` in its algebraic closure is the bottom intermediate field. -/
theorem baseField_padic : baseField p ℚ_[p] = ⊥ := by
  ext x
  simp [baseField, IntermediateField.mem_bot]

/-- A totally ramified extension of `ℚ_p` has the same residue field as `ℚ_p`. -/
instance hasSameResidueField_baseField_padic
    (F : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) [IsTotallyRamified ℚ_[p] F] :
    (baseField p ℚ_[p]).HasSameResidueField F := by
  rw [baseField_padic]
  infer_instance

end BaseField

section IntegralClosure

variable {K₀ : Type*} [NontriviallyNormedField K₀] [IsCompleteDiscreteValuedField K₀]
  {E E' : Type*} [Field E] [Field E'] [Algebra K₀ E] [Algebra K₀ E']
  [Algebra.IsAlgebraic K₀ E] [Algebra.IsAlgebraic K₀ E']

/-- The residue embedding induced by `e.symm` is inverse to the one induced by `e`. -/
theorem integralClosureResidueInclusion_symm_apply (e : E ≃ₐ[K₀] E')
    (z : integralClosureResidueField K₀ E) :
    integralClosureResidueInclusion K₀ e.symm.toAlgHom
      (integralClosureResidueInclusion K₀ e.toAlgHom z) = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [integralClosureResidueInclusion_residue, integralClosureResidueInclusion_residue]
  congr 1
  ext
  simp

/-- A `K₀`-isomorphism `E ≃ E'` induces an isomorphism over `𝓀[K₀]` of the residue fields of the
integral closures of `𝒪[K₀]` in `E` and in `E'`. -/
def integralClosureResidueFieldCongr (e : E ≃ₐ[K₀] E') :
    integralClosureResidueField K₀ E ≃ₐ[𝓀[K₀]] integralClosureResidueField K₀ E' :=
  AlgEquiv.ofAlgHom (integralClosureResidueInclusion K₀ e.toAlgHom)
    (integralClosureResidueInclusion K₀ e.symm.toAlgHom)
    (AlgHom.ext fun z ↦ by simpa using integralClosureResidueInclusion_symm_apply e.symm z)
    (AlgHom.ext (integralClosureResidueInclusion_symm_apply e))

end IntegralClosure

section Padic

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F]
  [FiniteDimensional ℚ_[p] F]

/-- The residue field of a finite extension of `ℚ_p` is finite. -/
instance finite_residueField_spectralIntegerRing :
    Finite (ResidueField (spectralIntegerRing ℚ_[p] F)) :=
  Module.finite_of_finite 𝓀[ℚ_[p]]

/-- The residue field of a finite totally ramified extension of `ℚ_p` has `p` elements. -/
instance fact_natCard_residueField_spectralIntegerRing [IsTotallyRamified ℚ_[p] F] :
    Fact (Nat.card (ResidueField (spectralIntegerRing ℚ_[p] F)) = p) := by
  have hs := (isTotallyRamified_iff_surjective_spectralIntegerRing ℚ_[p] F).mp ‹_›
  refine ⟨?_⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap 𝓀[ℚ_[p]] _).injective, hs⟩),
    Nat.card_congr (FalseTateExtension.padicResidueFieldEquiv p).toEquiv, Nat.card_zmod]

/-- `p ≠ 0` in the ring of integers of a finite extension of `ℚ_p`. -/
instance neZero_natCast_spectralIntegerRing : NeZero (p : spectralIntegerRing ℚ_[p] F) := by
  have := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  exact ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩

end Padic

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K] [NormedAlgebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

/-- The residue field of `K` is the residue field of its image in `K^alg`: the norm of `K` extends
the norm of `ℚ_p`, so `𝒪[K]` is the integral closure of `ℤ_p` in `K`. -/
def residueFieldBaseFieldEquiv : 𝓀[K] ≃+* integralClosureResidueField ℚ_[p] (baseField p K) :=
  (IsLocalRing.ResidueField.mapEquiv
    (IsIntegralClosure.equiv 𝒪[ℚ_[p]] 𝒪[K] K (integralClosure 𝒪[ℚ_[p]] K)).toRingEquiv).trans
    (integralClosureResidueFieldCongr (baseFieldEquiv p K)).toRingEquiv

variable (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsSeparable K L] [IsAPF K L]
  [Fact (¬ Module.Finite K L)] [IsTotallyRamified K L]
  (F : IntermediateField ℚ_[p] (AlgebraicClosure K)) [(baseField p K).HasSameResidueField F]

namespace IsLiftable

/-- The isomorphism `κ_L ≅ κ_F` of the residue field of `L` with the residue field of `F`: `κ_L`
is the residue field of `K` as `L/K` is totally ramified, and `F` has the same residue field as
`K` in `K^alg`. -/
def residueFieldEquiv :
    integralClosureResidueField K L ≃+* ResidueField (spectralIntegerRing ℚ_[p] F) :=
  (RingEquiv.ofBijective (algebraMap 𝓀[K] (integralClosureResidueField K L))
    ⟨(algebraMap 𝓀[K] _).injective, IsTotallyRamified.algebraMap_surjective⟩).symm.trans <|
  (residueFieldBaseFieldEquiv p K).trans <|
  (IntermediateField.HasSameResidueField.residueFieldEquiv (baseField p K) F).toRingEquiv.trans
    (integralClosureSpectralResidueEquiv ℚ_[p] (L := F)).toRingEquiv

/-- The coordinate family `(f_{g,u})_{g ∈ Aut(L/K)}` of the action of `Aut(L/K)` on `X_K(L)` in
the uniformizer `u`, with coefficients in `κ_F` through the isomorphism `κ_L ≅ κ_F`. -/
def coordinateFamily (u : FieldOfNorms K L)
    (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ)) :
    CoordinateFamily (ResidueField (spectralIntegerRing ℚ_[p] F)) (L ≃ₐ[K] L) :=
  (FieldOfNorms.coordinateFamily K L u hu).map (residueFieldEquiv p K L F)

variable {u : FieldOfNorms K L} (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ))

/-- The series of the coordinate family over `κ_F` are the images of the coordinate series
`f_{g,u}` under `κ_L ≅ κ_F`. -/
@[simp]
theorem coordinateFamily_series (g : L ≃ₐ[K] L) :
    (coordinateFamily p K L F u hu).series g =
      (FieldOfNorms.coordinateSeries K L u hu g).map (residueFieldEquiv p K L F) :=
  rfl

/-- The coefficients of the series of the coordinate family over `κ_F` are the images of the
coefficients of `f_{g,u}` under `κ_L ≅ κ_F`. -/
theorem coeff_coordinateFamily_series (g : L ≃ₐ[K] L) (n : ℕ) :
    coeff n ((coordinateFamily p K L F u hu).series g) =
      residueFieldEquiv p K L F (coeff n (FieldOfNorms.coordinateSeries K L u hu g)) := by
  rw [coordinateFamily_series, coeff_map]
  rfl

/-- The series of `g` in the coordinate family over `κ_F` is `T` if and only if `f_{g,u} = T`. -/
theorem coordinateFamily_series_eq_X_iff (g : L ≃ₐ[K] L) :
    (coordinateFamily p K L F u hu).series g = X ↔
      FieldOfNorms.coordinateSeries K L u hu g = X := by
  rw [coordinateFamily_series, ← map_X (residueFieldEquiv p K L F).toRingHom]
  exact (map_injective _ (residueFieldEquiv p K L F).injective).eq_iff

/-- `κ_L ≅ κ_F` preserves the order of `f_{g,u} - T`. -/
theorem order_coordinateFamily_series_sub_X (g : L ≃ₐ[K] L) :
    ((coordinateFamily p K L F u hu).series g - X).order =
      (FieldOfNorms.coordinateSeries K L u hu g - X).order := by
  rw [coordinateFamily, ← FieldOfNorms.coordinateFamily_series]
  exact (FieldOfNorms.coordinateFamily K L u hu).order_map_series_sub_X
    (φ := (residueFieldEquiv p K L F).toRingHom) (residueFieldEquiv p K L F).injective g

/-- `κ_L ≅ κ_F` preserves the ramification number `v_T(f_{g,u} - T) - 1`. -/
theorem ramificationNumber_coordinateFamily_series (g : L ≃ₐ[K] L) :
    ((coordinateFamily p K L F u hu).series g).ramificationNumber =
      (FieldOfNorms.coordinateSeries K L u hu g).ramificationNumber := by
  rw [coordinateFamily_series]
  exact ramificationNumber_map (φ := (residueFieldEquiv p K L F).toRingHom)
    (residueFieldEquiv p K L F).injective _

/-- The iterates of the series of the coordinate family over `κ_F` are the images of the iterates
of `f_{g,u}`. -/
theorem iterate_coordinateFamily_series (g : L ≃ₐ[K] L) (n : ℕ) :
    iterate ((coordinateFamily p K L F u hu).series g) n =
      (iterate (FieldOfNorms.coordinateSeries K L u hu g) n).map (residueFieldEquiv p K L F) :=
  (map_iterate _ ((FieldOfNorms.coordinateFamily K L u hu).hasSubst_series g) n).symm

/-- The series of `g` in the coordinate family over `κ_F` is tangent to the identity if and only
if `f_{g,u}` is. -/
theorem coeff_one_coordinateFamily_series_eq_one_iff (g : L ≃ₐ[K] L) :
    coeff 1 ((coordinateFamily p K L F u hu).series g) = 1 ↔
      coeff 1 (FieldOfNorms.coordinateSeries K L u hu g) = 1 := by
  rw [coeff_coordinateFamily_series]
  exact map_eq_one_iff _ (residueFieldEquiv p K L F).injective

/-- `κ_L ≅ κ_F` preserves the multiplicative order of the linear coefficient of `f_{g,u}`. -/
theorem orderOf_coeff_one_coordinateFamily_series (g : L ≃ₐ[K] L) :
    orderOf (coeff 1 ((coordinateFamily p K L F u hu).series g)) =
      orderOf (coeff 1 (FieldOfNorms.coordinateSeries K L u hu g)) := by
  rw [coeff_coordinateFamily_series]
  exact (residueFieldEquiv p K L F).toMulEquiv.orderOf_eq _

/-- `κ_L ≅ κ_F` preserves the order of the automorphism `a ↦ a ∘ f_{g,u}`. -/
theorem isOfFinOrder_substEquiv_coordinateFamily_series_iff (g : L ≃ₐ[K] L) :
    IsOfFinOrder (LaurentSeries.substEquiv ((coordinateFamily p K L F u hu).series g)) ↔
      IsOfFinOrder (LaurentSeries.substEquiv (FieldOfNorms.coordinateSeries K L u hu g)) := by
  rw [coordinateFamily, ← FieldOfNorms.coordinateFamily_series]
  exact (FieldOfNorms.coordinateFamily K L u hu).isOfFinOrder_substEquiv_map_series_iff
    (φ := (residueFieldEquiv p K L F).toRingHom) (residueFieldEquiv p K L F).injective g

end IsLiftable

variable [FiniteDimensional ℚ_[p] F]

/-- Yuan, Definition 1.1 (Berger 2014): the action of `Aut(L/K)` on the field of norms `X_K(L)` is
`F`-liftable, that is, there exist `P` and `(F_g)_{g ∈ Aut(L/K)}` in `A_K` with `P̄ = T^q`,
`ev_u(F̄_g) = g(u)`, `F_g ∘ P = P ∘ F_g` and `F_h ∘ F_g = F_{gh}` for all `g, h ∈ Aut(L/K)`. Here
`q` is the cardinality of `κ_F`, `u` is the uniformizer `FieldOfNorms.uniformizer K L` of `X_K(L)`
and `ev_u : κ_F((T)) ≅ X_K(L)` sends `T` to `u`, through `κ_F ≅ κ_L`. This does not depend on `u`
(Yuan, Proposition 2.3; `isLiftable_iff_uniformizer`). -/
def IsLiftable : Prop :=
  (IsLiftable.coordinateFamily p K L F (FieldOfNorms.uniformizer K L)
    (FieldOfNorms.valuation_uniformizer K L)).Liftable

namespace IsLiftable

variable {u u' : FieldOfNorms K L} (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ))
  (hu' : FieldOfNorms.valuation K L u' = WithZero.exp (-1 : ℤ))

/-- Yuan, Proposition 2.3: for two uniformizers `u` and `u'` of `X_K(L)`, the coordinate family in
`u'` has a lift to `A_K` if and only if the coordinate family in `u` has one. -/
theorem liftable_coordinateFamily_iff :
    (coordinateFamily p K L F u' hu').Liftable ↔ (coordinateFamily p K L F u hu).Liftable := by
  obtain ⟨V, hV0, hV1, hV⟩ := FieldOfNorms.exists_laurentEquiv_eq K L u hu hu'
  rw [coordinateFamily, coordinateFamily, FieldOfNorms.coordinateFamily_eq_conj K L u hu hu' hV,
    CoordinateFamily.map_conj _ _ hV0 hV1]
  exact CoordinateFamily.liftable_conj_iff _

/-- Yuan, Proposition 2.3 modulo `𝔪_F ^ (r + 1)`: for two uniformizers `u` and `u'` of `X_K(L)`
and a subset `S ⊆ Aut(L/K)`, the coordinate family in `u'` has a finite lift modulo
`𝔪_F ^ (r + 1)` on `S` if and only if the coordinate family in `u` has one. -/
theorem finiteLiftable_coordinateFamily_iff (S : Set (L ≃ₐ[K] L)) (r : ℕ) :
    (coordinateFamily p K L F u' hu').FiniteLiftable S r ↔
      (coordinateFamily p K L F u hu).FiniteLiftable S r := by
  obtain ⟨V, hV0, hV1, hV⟩ := FieldOfNorms.exists_laurentEquiv_eq K L u hu hu'
  rw [coordinateFamily, coordinateFamily, FieldOfNorms.coordinateFamily_eq_conj K L u hu hu' hV,
    CoordinateFamily.map_conj _ _ hV0 hV1]
  exact CoordinateFamily.finiteLiftable_conj_iff _

end IsLiftable

variable {u : FieldOfNorms K L} (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ))

/-- Yuan, Proposition 2.3: the action of `Aut(L/K)` on `X_K(L)` is `F`-liftable if and only if
the coordinate family in any given uniformizer `u` of `X_K(L)` has a lift to `A_K`. -/
theorem isLiftable_iff_uniformizer :
    IsLiftable p K L F ↔ (IsLiftable.coordinateFamily p K L F u hu).Liftable :=
  (IsLiftable.liftable_coordinateFamily_iff p K L F _ hu).symm

/-- `F`-liftability holds if and only if the coordinate family in some uniformizer of `X_K(L)` has
a lift to `A_K`. -/
theorem isLiftable_iff_exists_uniformizer :
    IsLiftable p K L F ↔ ∃ (u : FieldOfNorms K L)
      (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ)),
        (IsLiftable.coordinateFamily p K L F u hu).Liftable :=
  ⟨fun h ↦ ⟨_, _, h⟩, fun ⟨_, hu, h⟩ ↦ (isLiftable_iff_uniformizer p K L F hu).mpr h⟩

/-- `F`-liftability holds if and only if the coordinate family in every uniformizer of `X_K(L)`
has a lift to `A_K`. -/
theorem isLiftable_iff_forall_uniformizer :
    IsLiftable p K L F ↔ ∀ (u : FieldOfNorms K L)
      (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ)),
        (IsLiftable.coordinateFamily p K L F u hu).Liftable :=
  ⟨fun h _ hu ↦ (isLiftable_iff_uniformizer p K L F hu).mp h, fun h ↦ h _ _⟩

variable {p K L F} in
/-- An `F`-liftable action has, in every uniformizer `u` of `X_K(L)`, finite lifts modulo every
`𝔪_F ^ (r + 1)` on every subset of `Aut(L/K)`. -/
theorem IsLiftable.finiteLiftable (h : IsLiftable p K L F) (S : Set (L ≃ₐ[K] L)) (r : ℕ) :
    (IsLiftable.coordinateFamily p K L F u hu).FiniteLiftable S r :=
  ((isLiftable_iff_uniformizer p K L F hu).mp h).finiteLiftable S r

end FalseTateNonliftability
