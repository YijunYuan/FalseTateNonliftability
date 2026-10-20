/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition

/-!
# Coordinate families

Let a group `Γ` act on `κ((T))`, for a field `κ`, by continuous automorphisms over `κ` that
preserve the `T`-adic valuation. The image of the variable under `g ∈ Γ` is a power series
`f_g ∈ T κ⟦T⟧` with nonzero linear coefficient, the action on all of `κ((T))` is `a ↦ a ∘ f_g`,
and `f_{gh} = f_h ∘ f_g` (Yuan, Lemma 2.2). A coordinate family over a commutative ring `κ`,
indexed by a monoid `Γ`, is a family `(f_g)_{g ∈ Γ}` of power series with `f_g(0) = 0`, `f_g'(0)`
a unit and `f_{gh} = f_h ∘ f_g`. Then `f_1 = T` and `f_{g ^ n} = f_g^{∘n}`.

A ring homomorphism `φ : κ → κ'` applied to the coefficients gives a coordinate family over `κ'`;
for injective `φ` it preserves the `T`-adic order of every `f_g - T`. A change of variable
`T' = w(T)`, with `w(0) = 0` and `w'(0)` a unit, replaces `f_g` by `w ∘ f_g ∘ w^{∘-1}`
(Yuan, Lemma 2.2 (4)).

## Main definitions

* `FalseTateNonliftability.CoordinateFamily κ Γ`: families `(f_g)_{g ∈ Γ}` in `T κ⟦T⟧` with unit
  linear coefficients and `f_{gh} = f_h ∘ f_g`.
* `FalseTateNonliftability.CoordinateFamily.map φ f`: the family `(φ(f_g))_{g ∈ Γ}`.
* `FalseTateNonliftability.CoordinateFamily.conj w f`: the family `(w ∘ f_g ∘ w^{∘-1})_{g ∈ Γ}`.

## Main results

* `FalseTateNonliftability.CoordinateFamily.series_one`: `f_1 = T`.
* `FalseTateNonliftability.CoordinateFamily.series_pow`: `f_{g ^ n} = f_g^{∘n}`.
* `FalseTateNonliftability.CoordinateFamily.order_map_series_sub_X`: an injective coefficient
  map preserves the order of `f_g - T`.
* `FalseTateNonliftability.CoordinateFamily.conj_conj`,
  `FalseTateNonliftability.CoordinateFamily.conj_compInv_conj`: changing the variable by `w` and
  then by `v` is changing it by `v ∘ w`, and the change by `w^{∘-1}` undoes the change by `w`.
* `FalseTateNonliftability.CoordinateFamily.map_conj`: changes of coefficients and changes of
  variable commute.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.2.
-/

@[expose] public section

noncomputable section

open PowerSeries
open scoped PowerSeries

namespace FalseTateNonliftability

/-- A coordinate family over `κ` indexed by `Γ`: power series `f_g ∈ T κ⟦T⟧`, `g ∈ Γ`, with unit
linear coefficients and `f_{gh} = f_h ∘ f_g`. These are the series of the images of the variable
under an action of `Γ` on `κ((T))` (Yuan, Lemma 2.2). -/
structure CoordinateFamily (κ : Type*) [CommRing κ] (Γ : Type*) [Monoid Γ] where
  /-- The series `f_g`. -/
  series : Γ → κ⟦X⟧
  /-- `f_g(0) = 0`. -/
  constantCoeff_series (g : Γ) : (series g).constantCoeff = 0
  /-- `f_g'(0)` is a unit. -/
  isUnit_coeff_one_series (g : Γ) : IsUnit ((series g).coeff 1)
  /-- `f_{gh} = f_h ∘ f_g`. -/
  series_mul (g h : Γ) : series (g * h) = (series h).subst (series g)

namespace CoordinateFamily

variable {κ κ' κ'' : Type*} [CommRing κ] [CommRing κ'] [CommRing κ''] {Γ : Type*} [Monoid Γ]

@[ext]
theorem ext {f₁ f₂ : CoordinateFamily κ Γ} (h : ∀ g, f₁.series g = f₂.series g) : f₁ = f₂ := by
  obtain ⟨s₁, _, _, _⟩ := f₁
  obtain ⟨s₂, _, _, _⟩ := f₂
  obtain rfl : s₁ = s₂ := funext h
  rfl

variable (f : CoordinateFamily κ Γ)

theorem hasSubst_series (g : Γ) : HasSubst (f.series g) :=
  .of_constantCoeff_zero' (f.constantCoeff_series g)

/-- `f_1 = T`. -/
@[simp]
theorem series_one : f.series 1 = X := by
  set s := f.series 1
  have hs : s = subst s s := by simpa only [mul_one] using f.series_mul 1 1
  have hs0 := f.constantCoeff_series 1
  have hs1 := f.isUnit_coeff_one_series 1
  calc s = subst (subst s.compInv s) s := by rw [subst_compInv_right hs0 hs1, X_subst]
    _ = subst s.compInv (subst s s) :=
      (subst_comp_subst_apply (f.hasSubst_series 1) (HasSubst.compInv s) s).symm
    _ = X := by rw [← hs, subst_compInv_right hs0 hs1]

/-- `f_{g ^ n} = f_g^{∘n}`. -/
theorem series_pow (g : Γ) (n : ℕ) : f.series (g ^ n) = iterate (f.series g) n := by
  induction n with
  | zero => rw [pow_zero, series_one, iterate_zero]
  | succ n ih => rw [pow_succ', f.series_mul, ih, iterate_succ]

section Map

/-- The coordinate family `(φ(f_g))_{g ∈ Γ}` obtained by applying `φ` to the coefficients. -/
def map (φ : κ →+* κ') (f : CoordinateFamily κ Γ) : CoordinateFamily κ' Γ where
  series g := (f.series g).map φ
  constantCoeff_series g := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      f.constantCoeff_series, map_zero]
  isUnit_coeff_one_series g := by
    rw [coeff_map]
    exact (f.isUnit_coeff_one_series g).map φ
  series_mul g h := by
    rw [f.series_mul]
    exact map_subst (f.hasSubst_series g) _

@[simp]
theorem map_series (φ : κ →+* κ') (g : Γ) : (f.map φ).series g = (f.series g).map φ :=
  rfl

@[simp]
theorem map_id : f.map (RingHom.id κ) = f :=
  rfl

theorem map_map (φ : κ →+* κ') (ψ : κ' →+* κ'') : (f.map φ).map ψ = f.map (ψ.comp φ) :=
  rfl

/-- An injective coefficient map preserves the order of `f_g - T`, so it preserves the
ramification numbers `v_T(f_g - T) - 1`. -/
theorem order_map_series_sub_X {φ : κ →+* κ'} (hφ : Function.Injective φ) (g : Γ) :
    ((f.map φ).series g - X).order = (f.series g - X).order := by
  rw [map_series, ← map_X φ, ← map_sub]
  refine le_antisymm (le_order _ _ fun i hi ↦ hφ ?_) (le_order_map φ)
  rw [map_zero, ← coeff_map]
  exact coeff_of_lt_order i hi

end Map

section Conj

open scoped Classical in
/-- The coordinate family `(w ∘ f_g ∘ w^{∘-1})_{g ∈ Γ}` in the variable `T' = w(T)`, for `w` with
`w(0) = 0` and `w'(0)` a unit (Yuan, Lemma 2.2 (4)); it is `f` for every other `w`. -/
def conj (w : κ⟦X⟧) (f : CoordinateFamily κ Γ) : CoordinateFamily κ Γ :=
  if hw : w.constantCoeff = 0 ∧ IsUnit (w.coeff 1) then
    { series g := PowerSeries.conj w (f.series g)
      constantCoeff_series g := constantCoeff_conj hw.1 (f.constantCoeff_series g)
      isUnit_coeff_one_series g :=
        isUnit_coeff_one_conj hw.2 (f.constantCoeff_series g) (f.isUnit_coeff_one_series g)
      series_mul g h := by
        rw [f.series_mul, conj_subst hw.1 hw.2 (f.hasSubst_series h) (f.hasSubst_series g)] }
  else f

variable {w : κ⟦X⟧}

theorem conj_series (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) (g : Γ) :
    (f.conj w).series g = PowerSeries.conj w (f.series g) := by
  simp only [conj, hw, hw', and_self, dite_true]

theorem conj_of_not (hw : ¬(w.constantCoeff = 0 ∧ IsUnit (w.coeff 1))) : f.conj w = f := by
  simp only [conj, hw, dite_false]

@[simp]
theorem conj_X : f.conj X = f :=
  ext fun g ↦ by
    rw [conj_series f constantCoeff_X (by simp), PowerSeries.conj_X (f.hasSubst_series g)]

/-- Changing the variable by `w` and then by `v` is changing it by `v ∘ w`. -/
theorem conj_conj {v : κ⟦X⟧} (hv : v.constantCoeff = 0) (hv' : IsUnit (v.coeff 1))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    (f.conj w).conj v = f.conj (v.subst w) := by
  have hvw : constantCoeff (v.subst w) = 0 := by
    rw [constantCoeff_subst_of_constantCoeff_zero' hw, hv]
  have hvw' : IsUnit (coeff 1 (v.subst w)) := by
    rw [coeff_one_subst hw]
    exact hv'.mul hw'
  refine ext fun g ↦ ?_
  rw [conj_series _ hv hv', conj_series f hw hw', conj_series f hvw hvw',
    PowerSeries.conj_conj hv hv' hw hw' (f.hasSubst_series g)]

/-- The change of variable by `w^{∘-1}` undoes the change of variable by `w`. -/
@[simp]
theorem conj_compInv_conj (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    (f.conj w).conj w.compInv = f :=
  ext fun g ↦ by
    rw [conj_series _ (constantCoeff_compInv w) (isUnit_coeff_one_compInv w),
      conj_series f hw hw', PowerSeries.conj_compInv_conj hw hw' (f.hasSubst_series g)]

/-- The change of variable by `w` undoes the change of variable by `w^{∘-1}`. -/
@[simp]
theorem conj_conj_compInv (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    (f.conj w.compInv).conj w = f :=
  ext fun g ↦ by
    rw [conj_series _ hw hw', conj_series f (constantCoeff_compInv w) (isUnit_coeff_one_compInv w),
      PowerSeries.conj_conj_compInv hw hw' (f.hasSubst_series g)]

/-- Changes of coefficients commute with changes of variable. -/
theorem map_conj (φ : κ →+* κ') (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    (f.conj w).map φ = (f.map φ).conj (w.map φ) := by
  have hφw : (w.map φ).constantCoeff = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hw,
      map_zero]
  have hφw' : IsUnit ((w.map φ).coeff 1) := by
    rw [coeff_map]
    exact hw'.map φ
  refine ext fun g ↦ ?_
  rw [map_series, conj_series f hw hw', conj_series _ hφw hφw', map_series,
    PowerSeries.map_conj φ hw hw' (f.hasSubst_series g)]

end Conj

end CoordinateFamily

end FalseTateNonliftability
