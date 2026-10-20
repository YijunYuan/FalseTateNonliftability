/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.NormalForm
public import FalseTateNonliftability.PowerSeries.PrincipalUnits
public import FalseTateNonliftability.Liftability.CoordinateChange
public import FalseTateNonliftability.Liftability.FieldOfNorms
public import FalseTateExtension.Padic.Basic

/-!
# `F`-liftability of the action on the field of norms

Let `p` be a prime, `K` a finite extension of `ℚ_p` with algebraic closure `K^alg`, and `L ⊆ K^alg`
an infinite totally ramified APF extension of `K` with field of norms `X_K(L)`. Let `F ⊆ K^alg` be
a finite extension of `ℚ_p` with the same residue field as `K`, with ring of integers `𝒪_F`,
maximal ideal `𝔪_F` and residue field `κ_F` with `q` elements, and let `A_K` be the `𝔪_F`-adic
completion of `𝒪_F((T))`. As `L/K` is totally ramified, the residue field `κ_L` of `X_K(L)` is the
residue field of `K`, hence isomorphic to `κ_F`. For a uniformizer `u` of `X_K(L)`, the coordinate
series `f_{g,u}` of the elements `g ∈ Aut(L/K)` (`ev_u(f_{g,u}) = g(u)`, Yuan, §1.4) thus form a
coordinate family over `κ_F`. The action of `Aut(L/K)` on `X_K(L)` is `F`-liftable (Berger;
Yuan, Definition 1.1) if this family has a lift to `A_K`: there exist `P` and
`(F_g)_{g ∈ Aut(L/K)}` in `A_K` with `P̄ = T^q`, `ev_u(F̄_g) = g(u)`, `F_g ∘ P = P ∘ F_g` and
`F_h ∘ F_g = F_{gh}` for all `g, h ∈ Aut(L/K)`.

A change of uniformizer conjugates the coordinate family by a change of variable
(Yuan, Lemma 2.2 (4)), so `F`-liftability does not depend on the uniformizer, and neither does the
existence of finite lifts modulo `𝔪_F ^ (r + 1)` on a subset of `Aut(L/K)`
(Yuan, Proposition 2.3). The isomorphism `κ_L ≅ κ_F` preserves the ramification numbers
`v_T(f_{g,u} - T) - 1`, the multiplicative orders of the linear coefficients `f_{g,u}'(0)` and the
finiteness of the orders of the automorphisms `a ↦ a ∘ f_{g,u}` of `κ_L((T))`, which are the
arithmetic inputs of Yuan, §5.

For `K = ℚ_p`, a finite totally ramified extension `F/ℚ_p` has the same residue field as `ℚ_p`,
and `κ_F` has `p` elements.

## Main definitions

* `FalseTateNonliftability.baseField p K`: the image of `K` in `K^alg`, an intermediate field of
  `K^alg/ℚ_p`.
* `FalseTateNonliftability.IsLiftable.residueFieldEquiv p K L F`: the isomorphism `κ_L ≅ κ_F`.
* `FalseTateNonliftability.IsLiftable.coordinateFamily p K L F u hu`: the coordinate family
  `(f_{g,u})_{g ∈ Aut(L/K)}` over `κ_F`.
* `FalseTateNonliftability.IsLiftable p K L F`: the action of `Aut(L/K)` on `X_K(L)` is
  `F`-liftable (Yuan, Definition 1.1).

## Main results

* `FalseTateNonliftability.isLiftable_iff_uniformizer`,
  `FalseTateNonliftability.isLiftable_iff_exists_uniformizer`,
  `FalseTateNonliftability.isLiftable_iff_forall_uniformizer`,
  `FalseTateNonliftability.IsLiftable.liftable_coordinateFamily_iff`,
  `FalseTateNonliftability.IsLiftable.finiteLiftable_coordinateFamily_iff`: `F`-liftability and
  finite liftability do not depend on the uniformizer (Yuan, Proposition 2.3).
* `FalseTateNonliftability.IsLiftable.finiteLiftable`: an `F`-liftable action has finite lifts
  modulo every `𝔪_F ^ (r + 1)` on every subset of `Aut(L/K)`, in every uniformizer.
* `FalseTateNonliftability.hasSameResidueField_baseField_padic`: a totally ramified extension of
  `ℚ_p` has the same residue field as `ℚ_p`.
* `FalseTateNonliftability.fact_natCard_residueField_spectralIntegerRing`: the residue field of a
  finite totally ramified extension of `ℚ_p` has `p` elements.
* `FalseTateNonliftability.IsLiftable.ramificationNumber_coordinateFamily_series`,
  `FalseTateNonliftability.IsLiftable.orderOf_coeff_one_coordinateFamily_series`,
  `FalseTateNonliftability.IsLiftable.isOfFinOrder_substEquiv_coordinateFamily_series_iff`: the
  isomorphism `κ_L ≅ κ_F` preserves ramification numbers, the orders of the linear coefficients
  and the finiteness of the orders of the automorphisms `a ↦ a ∘ f_{g,u}`.

## Implementation notes

* `K` is a field with `[NormedAlgebra ℚ_[p] K]`, and `L` and `F` are intermediate fields of
  `K^alg = AlgebraicClosure K` over `K` and over `ℚ_p`. As the norm of `K` extends the norm of
  `ℚ_p`, `𝒪[K]` is the integral closure of `ℤ_p` in `K`, so the residue field of `K` is the
  residue field of `baseField p K`. "`F` has the same residue field as `K`" is the
  FontaineWintenberger class `(baseField p K).HasSameResidueField F`: the images of the residue
  fields of `K` and `F` in the residue field of the integral closure of `ℤ_p` in `K^alg` coincide.
  It provides the isomorphism `κ_L ≅ κ_F`.
* Total ramification of `L/K` and the same residue field condition are Prop classes of
  FontaineWintenberger and enter as instance arguments; the infiniteness of `L/K`, required by
  the field of norms of FontaineWintenberger, is the instance `Fact (¬ Module.Finite K L)`.
* `IsLiftable p K L F` uses the uniformizer `FieldOfNorms.uniformizer K L` of FontaineWintenberger;
  `isLiftable_iff_uniformizer` replaces it by any other uniformizer.
* Proposition 2.3 also states that liftability modulo every power of `ϖ_F`, with the composition
  law `F_h ∘ F_g = F_{gh}`, does not depend on the uniformizer. Of the statements modulo
  `𝔪_F ^ (r + 1)`, only the one for finite lifts (`CoordinateFamily.FiniteLift`: a lift of
  Frobenius commuting with lifts of the elements of a subset, without composition law) is
  formalized, `finiteLiftable_coordinateFamily_iff`; this is the form of Proposition 1.3.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  §1.4, Definition 1.1, Lemma 2.2 and Proposition 2.3.
* L. Berger, *Lifting the field of norms*, J. Éc. polytech. Math. 1 (2014), 29–38.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger PowerSeries
open IsLocalRing (ResidueField)
open scoped PowerSeries

namespace FalseTateNonliftability

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

/-- For a `K₀`-isomorphism `e : E ≃ E'`, the map of residue fields induced by `e⁻¹` is a left
inverse of the map induced by `e`. -/
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

/-- The isomorphism of the residue field of `K` with the residue field of the integral closure of
`ℤ_p` in the image of `K` in `K^alg`. Here `𝒪[K]` is the integral closure of `ℤ_p` in `K`, as the
norm of `K` extends the norm of `ℚ_p`. -/
def residueFieldBaseFieldEquiv : 𝓀[K] ≃+* integralClosureResidueField ℚ_[p] (baseField p K) :=
  (IsLocalRing.ResidueField.mapEquiv
    (IsIntegralClosure.equiv 𝒪[ℚ_[p]] 𝒪[K] K (integralClosure 𝒪[ℚ_[p]] K)).toRingEquiv).trans
    (integralClosureResidueFieldCongr (baseFieldEquiv p K)).toRingEquiv

variable (L : IntermediateField K (AlgebraicClosure K)) [Algebra.IsSeparable K L] [IsAPF K L]
  [Fact (¬ Module.Finite K L)] [IsTotallyRamified K L]
  (F : IntermediateField ℚ_[p] (AlgebraicClosure K)) [FiniteDimensional ℚ_[p] F]
  [(baseField p K).HasSameResidueField F]

section CoordinateFamily

omit [FiniteDimensional ℚ_[p] F]

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

/-- `κ_L ≅ κ_F` preserves the ramification number `v_T(f_{g,u} - T) - 1`. -/
theorem ramificationNumber_coordinateFamily_series (g : L ≃ₐ[K] L) :
    ((coordinateFamily p K L F u hu).series g).ramificationNumber =
      (FieldOfNorms.coordinateSeries K L u hu g).ramificationNumber := by
  rw [coordinateFamily_series]
  exact ramificationNumber_map (φ := (residueFieldEquiv p K L F).toRingHom)
    (residueFieldEquiv p K L F).injective _

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

/-- The automorphism `a ↦ a ∘ f_{g,u}` of `κ_F((T))`, with coefficients mapped by `κ_L ≅ κ_F`, has
finite order if and only if `a ↦ a ∘ f_{g,u}` of `κ_L((T))` has finite order. -/
theorem isOfFinOrder_substEquiv_coordinateFamily_series_iff (g : L ≃ₐ[K] L) :
    IsOfFinOrder (LaurentSeries.substEquiv ((coordinateFamily p K L F u hu).series g)) ↔
      IsOfFinOrder (LaurentSeries.substEquiv (FieldOfNorms.coordinateSeries K L u hu g)) := by
  rw [coordinateFamily, ← FieldOfNorms.coordinateFamily_series]
  exact (FieldOfNorms.coordinateFamily K L u hu).isOfFinOrder_substEquiv_map_series_iff
    (φ := (residueFieldEquiv p K L F).toRingHom) (residueFieldEquiv p K L F).injective g

end IsLiftable

end CoordinateFamily

/-- Yuan, Definition 1.1 (Berger 2014): the action of `Aut(L/K)` on the field of norms `X_K(L)` is
`F`-liftable, that is, there exist `P` and `(F_g)_{g ∈ Aut(L/K)}` in the `𝔪_F`-adic completion
`A_K` of `𝒪_F((T))` with `P̄ = T^q`, `ev_u(F̄_g) = g(u)`, `F_g ∘ P = P ∘ F_g` and
`F_h ∘ F_g = F_{gh}` for all `g, h ∈ Aut(L/K)`. Here `q` is the cardinality of the residue field
`κ_F` of `F`, `u` is a fixed uniformizer of `X_K(L)` and `ev_u : κ_F((T)) ≅ X_K(L)` sends `T` to
`u`, through `κ_F ≅ κ_L`. This does not depend on `u` (Yuan, Proposition 2.3). -/
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

/-- Yuan, Proposition 2.3 modulo `𝔪_F ^ (r + 1)`, for a lift of Frobenius commuting with lifts of
a prescribed collection of elements: for two uniformizers `u` and `u'` of `X_K(L)` and a subset
`S ⊆ Aut(L/K)`, the coordinate family in `u'` has a finite lift modulo `𝔪_F ^ (r + 1)` on `S`
(elements `P` and `F_g`, `g ∈ S`, with `P̄ = T^q`, `F̄_g = f_{g,u'}` and `F_g ∘ P = P ∘ F_g`) if and
only if the coordinate family in `u` has one. -/
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

/-- Yuan, Proposition 2.3: `F`-liftability holds if and only if the coordinate family in some
uniformizer of `X_K(L)` has a lift to `A_K`. -/
theorem isLiftable_iff_exists_uniformizer :
    IsLiftable p K L F ↔ ∃ (u : FieldOfNorms K L)
      (hu : FieldOfNorms.valuation K L u = WithZero.exp (-1 : ℤ)),
        (IsLiftable.coordinateFamily p K L F u hu).Liftable :=
  ⟨fun h ↦ ⟨_, _, h⟩, fun ⟨_, hu, h⟩ ↦ (isLiftable_iff_uniformizer p K L F hu).mpr h⟩

/-- Yuan, Proposition 2.3: `F`-liftability holds if and only if the coordinate family in every
uniformizer of `X_K(L)` has a lift to `A_K`. -/
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
