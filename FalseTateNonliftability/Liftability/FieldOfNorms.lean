/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Substitution
public import FalseTateNonliftability.Liftability.CoordinateFamily
public import FontaineWintenberger.FieldOfNorms.Estimates.Transfer
public import FontaineWintenberger.FieldOfNorms.Structure.Laurent
public import FontaineWintenberger.Mathlib.Topology.LaurentSubstitution
public import FontaineWintenberger.Ramification.Fields.TotallyRamified

/-!
# The coordinate family of the field of norms

Let `K` be a complete discretely valued field with perfect residue field of characteristic `p`,
let `L/K` be an infinite separable APF extension, and let `X_K(L)` be the field of norms of
Fontaine and Wintenberger, a complete discretely valued field of characteristic `p` with
valuation `v` on which `Aut(L/K)` acts by continuous automorphisms. Let `κ_L` be the residue field
of the integral closure of `𝒪[K]` in `L`; it is the residue field of `X_K(L)` and embeds in
`X_K(L)` as the field of constants. For a uniformizer `u` of `X_K(L)` let
`ev_u : κ_L((T)) ≃ X_K(L)` be the isomorphism over `κ_L` sending `T` to `u`. The coordinate series
of `g ∈ Aut(L/K)` is the power series `f_{g,u} ∈ κ_L⟦T⟧` with `ev_u(f_{g,u}) = g(u)`
(Yuan, §1.4).

Since `g(u)` is again a uniformizer, `f_{g,u}(0) = 0` and `f_{g,u}'(0) ≠ 0` (Yuan, Lemma 2.2 (1)).
If `L/K` is totally ramified, then `Aut(L/K)` fixes the constants `κ_L ⊆ X_K(L)`, and
(Yuan, Lemma 2.2 (2)–(4)):
* `g(ev_u(a)) = ev_u(a ∘ f_{g,u})` for every `a ∈ κ_L((T))`;
* `f_{gh,u} = f_{h,u} ∘ f_{g,u}`, so the `f_{g,u}` form a coordinate family indexed by `Aut(L/K)`;
* if `u' = ev_u(V)` is another uniformizer, then `f_{g,u'} = V ∘ f_{g,u} ∘ V^{∘-1}`.

## Main definitions

* `FalseTateNonliftability.FieldOfNorms.coordinateSeries K L u hu g`: the coordinate series
  `f_{g,u}`.
* `FalseTateNonliftability.FieldOfNorms.coordinateFamily K L u hu`: the coordinate family
  `(f_{g,u})_{g ∈ Aut(L/K)}`.

## Main results

* `FalseTateNonliftability.FieldOfNorms.laurentEquiv_coordinateSeries`: `ev_u(f_{g,u}) = g(u)`.
* `FalseTateNonliftability.FieldOfNorms.aut_residueConstants`: for `L/K` totally ramified,
  `Aut(L/K)` fixes the constants of `X_K(L)`.
* `FalseTateNonliftability.FieldOfNorms.valuation_ofPowerSeries_coordinateSeries`,
  `FalseTateNonliftability.FieldOfNorms.constantCoeff_coordinateSeries`,
  `FalseTateNonliftability.FieldOfNorms.isUnit_coeff_one_coordinateSeries`: Yuan, Lemma 2.2 (1).
* `FalseTateNonliftability.FieldOfNorms.aut_laurentEquiv`: Yuan, Lemma 2.2 (2).
* `FalseTateNonliftability.FieldOfNorms.coordinateSeries_mul`: Yuan, Lemma 2.2 (3).
* `FalseTateNonliftability.FieldOfNorms.exists_laurentEquiv_eq`: every uniformizer is `ev_u(V)`
  with `V(0) = 0` and `V'(0) ≠ 0`.
* `FalseTateNonliftability.FieldOfNorms.laurentEquiv_substEquiv`: `ev_u(a ∘ V) = ev_{u'}(a)` for
  `u' = ev_u(V)`.
* `FalseTateNonliftability.FieldOfNorms.coordinateSeries_eq_conj`,
  `FalseTateNonliftability.FieldOfNorms.coordinateFamily_eq_conj`: Yuan, Lemma 2.2 (4).

## Implementation notes

A uniformizer of `X_K(L)` is an element `u` together with a proof `hu : v(u) = exp (-1)`, as in
the isomorphism `ev_u = FieldOfNorms.laurentEquiv K L u hu` of FontaineWintenberger; the
coordinate series take the same two arguments.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  §1.4 and Lemma 2.2.
* J.-P. Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Ann. Sci. École Norm. Sup. (4) 16 (1983), 59–89.
-/

@[expose] public section

noncomputable section

open FontaineWintenberger LaurentSeries PowerSeries WithZero
open scoped PowerSeries

namespace FalseTateNonliftability

/-- `exp (-1) ≤ 1` in `ℤᵐ⁰`. -/
private theorem exp_neg_one_le_one : exp (-1 : ℤ) ≤ (1 : ℤᵐ⁰) := by
  rw [← exp_zero]
  exact exp_le_exp.mpr (by omega)

section Field

variable {k : Type*} [Field k]

/-- A Laurent series of valuation at most `1` is the power series of its coefficients. -/
private theorem ofPowerSeries_mk_coeff {A : LaurentSeries k} (hA : Valued.v A ≤ 1) :
    HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n ↦ A.coeff n) = A := by
  obtain ⟨w, rfl⟩ := (LaurentSeries.val_le_one_iff_eq_coe k A).mp hA
  congr 1
  ext n
  rw [coeff_mk, HahnSeries.ofPowerSeries_apply_coeff]

/-- A power series of `T`-adic valuation `1` has zero constant coefficient and nonzero linear
coefficient. -/
private theorem constantCoeff_eq_zero_and_isUnit_coeff_one {P : PowerSeries k}
    (hP : Valued.v (HahnSeries.ofPowerSeries ℤ k P) = exp (-1 : ℤ)) :
    P.constantCoeff = 0 ∧ IsUnit (P.coeff 1) := by
  have hzero : P.constantCoeff = 0 := by
    have hc := LaurentSeries.coeff_zero_of_lt_valuation k hP.le (show (0 : ℤ) < 1 by omega)
    simpa [PowerSeries.coeff_coe] using hc
  refine ⟨hzero, isUnit_iff_ne_zero.mpr fun hlinear ↦ ?_⟩
  have hcoeff (n : ℤ) (hn : n < 2) : (HahnSeries.ofPowerSeries ℤ k P).coeff n = 0 := by
    rw [PowerSeries.coeff_coe]
    split_ifs with hn0
    · rfl
    · rcases (show n.natAbs = 0 ∨ n.natAbs = 1 by omega) with h | h <;> rw [h]
      · simpa using hzero
      · exact hlinear
  have hbound : Valued.v (HahnSeries.ofPowerSeries ℤ k P) ≤ exp (-2 : ℤ) :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k).mpr hcoeff
  rw [hP] at hbound
  exact not_le_of_gt (exp_lt_exp.mpr (by omega : (-2 : ℤ) < -1)) hbound

/-- A continuous ring endomorphism of `k((T))` fixing `k` and sending `T` to a power series `f`
with `f(0) = 0` and `f'(0)` a unit is the substitution `a ↦ a ∘ f`. -/
private theorem eq_substEquiv_apply_of_continuous (F : LaurentSeries k →+* LaurentSeries k)
    (hF : Continuous F) (hC : ∀ a, F (HahnSeries.C a) = HahnSeries.C a) {f : PowerSeries k}
    (hf : f.constantCoeff = 0) (hf' : IsUnit (f.coeff 1))
    (hX : F (HahnSeries.single (1 : ℤ) (1 : k)) = HahnSeries.ofPowerSeries ℤ k f)
    (A : LaurentSeries k) : F A = substEquiv f A := by
  have h : F = ((substEquiv f).toRingEquiv : LaurentSeries k →+* LaurentSeries k) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries k))
      (RingHom.ext fun P ↦ ?_)
    simp only [RingHom.comp_apply, LaurentSeries.coe_algebraMap, RingHom.coe_coe,
      AlgEquiv.coe_toRingEquiv]
    rw [map_ofPowerSeries_eq_subst F hF hC f hf hX P, substEquiv_ofPowerSeries hf hf' P]
  exact RingHom.congr_fun h A

end Field

namespace FieldOfNorms

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L]
  [Fact (¬ Module.Finite K L)]

/-- For a totally ramified extension `L/K`, every `g ∈ Aut(L/K)` fixes the constants
`κ_L ⊆ X_K(L)`. -/
theorem aut_residueConstants [IsTotallyRamified K L] (g : L ≃ₐ[K] L)
    (a : integralClosureResidueField K L) :
    FieldOfNorms.aut K L g (residueConstants K L a) = residueConstants K L a := by
  rw [FieldOfNorms.aut_apply, FieldOfNorms.mapEquiv_residueConstants]
  congr 1
  obtain ⟨b, rfl⟩ := IsTotallyRamified.algebraMap_surjective (K := K) (L := L) a
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective b
  rw [IsLocalRing.ResidueField.algebraMap_residue, algebraicResidueAut_residue,
    AlgEquiv.commutes]

variable (u : FieldOfNorms K L) (hu : FieldOfNorms.valuation K L u = exp (-1 : ℤ))

/-- The coordinate series `f_{g,u} ∈ κ_L⟦T⟧` of `g ∈ Aut(L/K)` in the uniformizer `u` of
`X_K(L)`: the power series with `ev_u(f_{g,u}) = g(u)` (Yuan, §1.4). -/
def coordinateSeries (g : L ≃ₐ[K] L) : PowerSeries (integralClosureResidueField K L) :=
  PowerSeries.mk fun n ↦
    ((FieldOfNorms.laurentEquiv K L u hu).symm (FieldOfNorms.aut K L g u)).coeff n

section Coordinates

/-- `ev_u(f_{g,u}) = g(u)`. -/
@[simp]
theorem laurentEquiv_coordinateSeries (g : L ≃ₐ[K] L) :
    FieldOfNorms.laurentEquiv K L u hu
      (HahnSeries.ofPowerSeries ℤ _ (coordinateSeries K L u hu g)) =
        FieldOfNorms.aut K L g u := by
  have hv : Valued.v ((FieldOfNorms.laurentEquiv K L u hu).symm (FieldOfNorms.aut K L g u)) =
      exp (-1 : ℤ) := by
    rw [← FieldOfNorms.laurentEquiv_valuation K L u hu, RingEquiv.apply_symm_apply,
      FieldOfNorms.aut_valuation, hu]
  rw [coordinateSeries, ofPowerSeries_mk_coeff (hv.le.trans exp_neg_one_le_one),
    RingEquiv.apply_symm_apply]

/-- `f_{g,u}` is the only power series whose evaluation at `u` is `g(u)`. -/
theorem coordinateSeries_eq_iff (g : L ≃ₐ[K] L)
    (P : PowerSeries (integralClosureResidueField K L)) :
    coordinateSeries K L u hu g = P ↔
      FieldOfNorms.laurentEquiv K L u hu (HahnSeries.ofPowerSeries ℤ _ P) =
        FieldOfNorms.aut K L g u := by
  rw [← laurentEquiv_coordinateSeries K L u hu g,
    (FieldOfNorms.laurentEquiv K L u hu).injective.eq_iff,
    HahnSeries.ofPowerSeries_injective.eq_iff, eq_comm]

/-- `g(u)` is a uniformizer: `v_T(f_{g,u}) = 1` (Yuan, Lemma 2.2 (1)). -/
theorem valuation_ofPowerSeries_coordinateSeries (g : L ≃ₐ[K] L) :
    Valued.v (HahnSeries.ofPowerSeries ℤ _ (coordinateSeries K L u hu g)) = exp (-1 : ℤ) := by
  rw [← FieldOfNorms.laurentEquiv_valuation K L u hu, laurentEquiv_coordinateSeries,
    FieldOfNorms.aut_valuation, hu]

/-- `f_{g,u}(0) = 0` (Yuan, Lemma 2.2 (1)). -/
theorem constantCoeff_coordinateSeries (g : L ≃ₐ[K] L) :
    (coordinateSeries K L u hu g).constantCoeff = 0 :=
  (constantCoeff_eq_zero_and_isUnit_coeff_one
    (valuation_ofPowerSeries_coordinateSeries K L u hu g)).1

/-- The linear coefficient of `f_{g,u}` is nonzero (Yuan, Lemma 2.2 (1)). -/
theorem isUnit_coeff_one_coordinateSeries (g : L ≃ₐ[K] L) :
    IsUnit ((coordinateSeries K L u hu g).coeff 1) :=
  (constantCoeff_eq_zero_and_isUnit_coeff_one
    (valuation_ofPowerSeries_coordinateSeries K L u hu g)).2

variable {u' : FieldOfNorms K L} (hu' : FieldOfNorms.valuation K L u' = exp (-1 : ℤ))
include hu'

/-- Every uniformizer `u'` of `X_K(L)` is `ev_u(V)` for a power series `V` with `V(0) = 0` and
`V'(0) ≠ 0`. -/
theorem exists_laurentEquiv_eq :
    ∃ V : PowerSeries (integralClosureResidueField K L), V.constantCoeff = 0 ∧
      IsUnit (V.coeff 1) ∧
        FieldOfNorms.laurentEquiv K L u hu (HahnSeries.ofPowerSeries ℤ _ V) = u' := by
  have hv : Valued.v ((FieldOfNorms.laurentEquiv K L u hu).symm u') = exp (-1 : ℤ) := by
    rw [← FieldOfNorms.laurentEquiv_valuation K L u hu, RingEquiv.apply_symm_apply, hu']
  have hV := ofPowerSeries_mk_coeff (hv.le.trans exp_neg_one_le_one)
  rw [← hV] at hv
  exact ⟨_, (constantCoeff_eq_zero_and_isUnit_coeff_one hv).1,
    (constantCoeff_eq_zero_and_isUnit_coeff_one hv).2, by rw [hV, RingEquiv.apply_symm_apply]⟩

variable {V : PowerSeries (integralClosureResidueField K L)}
  (hV : FieldOfNorms.laurentEquiv K L u hu (HahnSeries.ofPowerSeries ℤ _ V) = u')
include hV

/-- A power series `V` with `ev_u(V)` a uniformizer has `V(0) = 0` and `V'(0) ≠ 0`. -/
private theorem constantCoeff_eq_zero_and_isUnit_coeff_one_of_laurentEquiv_eq :
    V.constantCoeff = 0 ∧ IsUnit (V.coeff 1) :=
  constantCoeff_eq_zero_and_isUnit_coeff_one (by
    rw [← FieldOfNorms.laurentEquiv_valuation K L u hu, hV, hu'])

/-- Change of uniformizer: if `u' = ev_u(V)`, then `ev_u(a ∘ V) = ev_{u'}(a)` for every
`a ∈ κ_L((T))`. -/
theorem laurentEquiv_substEquiv (A : LaurentSeries (integralClosureResidueField K L)) :
    FieldOfNorms.laurentEquiv K L u hu (substEquiv V A) =
      FieldOfNorms.laurentEquiv K L u' hu' A := by
  set e := FieldOfNorms.laurentEquiv K L u hu
  set e' := FieldOfNorms.laurentEquiv K L u' hu'
  obtain ⟨hV0, hV1⟩ :=
    constantCoeff_eq_zero_and_isUnit_coeff_one_of_laurentEquiv_eq K L u hu hu' hV
  let F : LaurentSeries _ →+* LaurentSeries _ := (e'.trans e.symm).toRingHom
  have hF : Continuous F :=
    (FieldOfNorms.continuous_laurentEquiv_symm K L u hu).comp
      (FieldOfNorms.continuous_laurentEquiv K L u' hu')
  have hC (a : integralClosureResidueField K L) : F (HahnSeries.C a) = HahnSeries.C a := by
    apply e.injective
    simp only [F, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, e, e', ← LaurentSeries.algebraMap_apply,
      FieldOfNorms.laurentEquiv_C]
  have hX : F (HahnSeries.single 1 1) = HahnSeries.ofPowerSeries ℤ _ V := by
    apply e.injective
    rw [hV]
    simp only [F, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, e', ← HahnSeries.ofPowerSeries_X,
      ← LaurentSeries.coe_algebraMap, FieldOfNorms.laurentEquiv_X]
  rw [← eq_substEquiv_apply_of_continuous F hF hC hV0 hV1 hX A]
  simp only [F, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]

end Coordinates

section Action

variable [IsTotallyRamified K L]

/-- `g(ev_u(a)) = ev_u(a ∘ f_{g,u})` for every `a ∈ κ_L((T))` (Yuan, Lemma 2.2 (2)). -/
theorem aut_laurentEquiv (g : L ≃ₐ[K] L) (A : LaurentSeries (integralClosureResidueField K L)) :
    FieldOfNorms.aut K L g (FieldOfNorms.laurentEquiv K L u hu A) =
      FieldOfNorms.laurentEquiv K L u hu (substEquiv (coordinateSeries K L u hu g) A) := by
  set e := FieldOfNorms.laurentEquiv K L u hu
  let F : LaurentSeries _ →+* LaurentSeries _ :=
    ((e.trans (FieldOfNorms.aut K L g)).trans e.symm).toRingHom
  have hF : Continuous F :=
    (FieldOfNorms.continuous_laurentEquiv_symm K L u hu).comp
      ((FieldOfNorms.uniformContinuous_mapEquiv g).continuous.comp
        (FieldOfNorms.continuous_laurentEquiv K L u hu))
  have hC (a : integralClosureResidueField K L) : F (HahnSeries.C a) = HahnSeries.C a := by
    apply e.injective
    simp only [F, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, e, ← LaurentSeries.algebraMap_apply,
      FieldOfNorms.laurentEquiv_C, residueConstantsFieldEmbedding_apply, aut_residueConstants]
  have hX : F (HahnSeries.single 1 1) =
      HahnSeries.ofPowerSeries ℤ _ (coordinateSeries K L u hu g) := by
    apply e.injective
    rw [show e (HahnSeries.ofPowerSeries ℤ _ (coordinateSeries K L u hu g)) = _ from
      laurentEquiv_coordinateSeries K L u hu g]
    simp only [F, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, e, ← HahnSeries.ofPowerSeries_X,
      ← LaurentSeries.coe_algebraMap, FieldOfNorms.laurentEquiv_X]
  rw [← eq_substEquiv_apply_of_continuous F hF hC (constantCoeff_coordinateSeries K L u hu g)
    (isUnit_coeff_one_coordinateSeries K L u hu g) hX A]
  simp only [F, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]

/-- `f_{gh,u} = f_{h,u} ∘ f_{g,u}` (Yuan, Lemma 2.2 (3)). -/
theorem coordinateSeries_mul (g h : L ≃ₐ[K] L) :
    coordinateSeries K L u hu (g * h) =
      (coordinateSeries K L u hu h).subst (coordinateSeries K L u hu g) := by
  rw [coordinateSeries_eq_iff,
    ← substEquiv_ofPowerSeries (constantCoeff_coordinateSeries K L u hu g)
      (isUnit_coeff_one_coordinateSeries K L u hu g),
    ← aut_laurentEquiv, laurentEquiv_coordinateSeries, map_mul, RingAut.mul_apply]

/-- The coordinate family `(f_{g,u})_{g ∈ Aut(L/K)}` of the action of `Aut(L/K)` on `X_K(L)` in
the uniformizer `u` (Yuan, Lemma 2.2). -/
def coordinateFamily : CoordinateFamily (integralClosureResidueField K L) (L ≃ₐ[K] L) where
  series := coordinateSeries K L u hu
  constantCoeff_series := constantCoeff_coordinateSeries K L u hu
  isUnit_coeff_one_series := isUnit_coeff_one_coordinateSeries K L u hu
  series_mul := coordinateSeries_mul K L u hu

/-- The series of the coordinate family in `u` are the coordinate series `f_{g,u}`. -/
@[simp]
theorem coordinateFamily_series (g : L ≃ₐ[K] L) :
    (coordinateFamily K L u hu).series g = coordinateSeries K L u hu g :=
  rfl

variable {u' : FieldOfNorms K L} (hu' : FieldOfNorms.valuation K L u' = exp (-1 : ℤ))
  {V : PowerSeries (integralClosureResidueField K L)}
  (hV : FieldOfNorms.laurentEquiv K L u hu (HahnSeries.ofPowerSeries ℤ _ V) = u')
include hu' hV

/-- Change of uniformizer: if `u' = ev_u(V)`, then `f_{g,u'} = V ∘ f_{g,u} ∘ V^{∘-1}`
(Yuan, Lemma 2.2 (4)). -/
theorem coordinateSeries_eq_conj (g : L ≃ₐ[K] L) :
    coordinateSeries K L u' hu' g = PowerSeries.conj V (coordinateSeries K L u hu g) := by
  obtain ⟨hV0, hV1⟩ :=
    constantCoeff_eq_zero_and_isUnit_coeff_one_of_laurentEquiv_eq K L u hu hu' hV
  refine ((conj_eq_iff_subst hV0 hV1).mpr ?_).symm
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  apply (FieldOfNorms.laurentEquiv K L u hu).injective
  rw [← substEquiv_ofPowerSeries (constantCoeff_coordinateSeries K L u hu g)
      (isUnit_coeff_one_coordinateSeries K L u hu g),
    ← aut_laurentEquiv, hV, ← substEquiv_ofPowerSeries hV0 hV1,
    laurentEquiv_substEquiv K L u hu hu' hV, laurentEquiv_coordinateSeries]

/-- Change of uniformizer: if `u' = ev_u(V)`, then the coordinate family in `u'` is the coordinate
family in `u` conjugated by `V` (Yuan, Lemma 2.2 (4)). -/
theorem coordinateFamily_eq_conj :
    coordinateFamily K L u' hu' = (coordinateFamily K L u hu).conj V := by
  obtain ⟨hV0, hV1⟩ :=
    constantCoeff_eq_zero_and_isUnit_coeff_one_of_laurentEquiv_eq K L u hu hu' hV
  refine CoordinateFamily.ext fun g ↦ ?_
  rw [CoordinateFamily.conj_series _ hV0 hV1, coordinateFamily_series, coordinateFamily_series,
    coordinateSeries_eq_conj K L u hu hu' hV]

end Action

end FieldOfNorms

end FalseTateNonliftability
