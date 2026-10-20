/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination

/-!
# Iterates, compositional inverses and conjugates of power series

Let `R` be a commutative ring. For power series `f, g ∈ R⟦X⟧` with `f(0)` nilpotent, write
`g ∘ f = g.subst f` for the composite `g(f(X))`. Composition is associative
(`PowerSeries.subst_comp_subst_apply`) with two-sided identity `X`, and a series `w` with
`w(0) = 0` and invertible linear coefficient `w'(0)` has a two-sided compositional inverse
`w^{∘-1}` (`PowerSeries.substInvOfIsUnit`). This file studies the iterates `f^{∘n}`, the
compositional inverse and the conjugates `w ∘ f ∘ w^{∘-1}`, their low-degree coefficients, and
their compatibility with ring homomorphisms `R → S` applied to the coefficients.

Conjugation is a change of variable. Let `σ` be a continuous automorphism of `k((T))` over a
field `k` with `σ T = f(T)`, and let `T' = w(T)` with `w(0) = 0` and `w'(0) ≠ 0`. Then
`σ T' = (w ∘ f ∘ w^{∘-1})(T')`, so `w ∘ f ∘ w^{∘-1}` is the series of `σ` in the variable `T'`
(Yuan, Lemma 2.2 (4)). Conjugation by `w` preserves composition and iterates.

This file is a candidate for upstreaming to Mathlib
(`Mathlib.RingTheory.PowerSeries.Substitution`).

## Main definitions

* `PowerSeries.iterate f n`: the `n`-fold composite `f^{∘n} = f ∘ ⋯ ∘ f`, with `f^{∘0} = X`.
* `PowerSeries.compInv w`: the compositional inverse `w^{∘-1}` of `w`.
* `PowerSeries.conj w f`: the conjugate `w ∘ f ∘ w^{∘-1}` of `f` by `w`.

## Main results

* `PowerSeries.iterate_add`, `PowerSeries.iterate_mul`: `f^{∘(m + n)} = f^{∘m} ∘ f^{∘n}` and
  `f^{∘(m * n)} = (f^{∘m})^{∘n}`.
* `PowerSeries.coeff_one_iterate`: the linear coefficient of `f^{∘n}` is the `n`-th power of the
  linear coefficient of `f`.
* `PowerSeries.coeff_subst_eq_sum`, `PowerSeries.coeff_subst_sub_coeff_of_dvd_inner`,
  `PowerSeries.coeff_subst_sub_coeff_of_dvd_outer`, `PowerSeries.coeff_iterate_sub_X`: low-degree
  coefficients of `f ∘ g` and `f^{∘n}` when `f` or `g` is `X` modulo `X ^ N`.
* `PowerSeries.continuous_subst_of_constantCoeff_zero`: over a discrete ring, `f ↦ f ∘ a` is
  continuous for the topology of coefficientwise convergence.
* `PowerSeries.subst_compInv_right`, `PowerSeries.subst_compInv_left`:
  `w ∘ w^{∘-1} = w^{∘-1} ∘ w = X`.
* `PowerSeries.map_compInv`: for a ring homomorphism `φ` applied to the coefficients,
  `φ(w^{∘-1}) = φ(w)^{∘-1}` (Yuan, Lemma 2.1 (3)).
* `PowerSeries.map_iterate`, `PowerSeries.map_conj`: `φ(f^{∘n}) = φ(f)^{∘n}` and
  `φ(w ∘ f ∘ w^{∘-1}) = φ(w) ∘ φ(f) ∘ φ(w)^{∘-1}`.
* `PowerSeries.conj_eq_iff_subst`: `w ∘ f ∘ w^{∘-1} = h` if and only if `w ∘ f = h ∘ w`.
* `PowerSeries.conj_subst`, `PowerSeries.conj_iterate`, `PowerSeries.conj_conj`: conjugation by
  `w` preserves composition and iterates, and conjugating by `w` and then by `v` is conjugating
  by `v ∘ w`.

## Implementation notes

`PowerSeries.compInv w` is defined for every `w`: it is `PowerSeries.substInvOfIsUnit w` if the
linear coefficient of `w` is a unit, and `X` otherwise. Its properties assume `w(0) = 0` and
`w'(0)` a unit. In this way `PowerSeries.compInv` and `PowerSeries.conj` take no hypotheses as
arguments.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.1 (3) (compositional inverses and reduction of coefficients), Lemma 2.2 (3), (4)
  (iterates and conjugates), proof of Lemma 5.3 (coefficients of `f ∘ g` and `f^{∘N}` in degree
  `d + 1`).
-/

@[expose] public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

section Subst

/-- If `f(0)` and `g(0)` are nilpotent, then so is `(g ∘ f)(0)`. -/
protected theorem HasSubst.subst {f g : R⟦X⟧} (hg : HasSubst g) (hf : HasSubst f) :
    HasSubst (g.subst f) := by
  simpa only [coe_substAlgHom] using hg.comp hf

/-- If `f(0) = 0`, then `(g ∘ f)(0) = g(0)`. -/
theorem constantCoeff_subst_of_constantCoeff_zero' {f : R⟦X⟧} (hf : f.constantCoeff = 0)
    (g : R⟦X⟧) : constantCoeff (g.subst f) = g.constantCoeff :=
  constantCoeff_subst_of_constantCoeff_zero hf g

/-- The chain rule at `0`: if `f(0) = 0`, then `(g ∘ f)'(0) = g'(0) f'(0)`. -/
theorem coeff_one_subst {f : R⟦X⟧} (hf : f.constantCoeff = 0) (g : R⟦X⟧) :
    coeff 1 (g.subst f) = g.coeff 1 * f.coeff 1 := by
  rw [coeff_subst' (.of_constantCoeff_zero' hf), finsum_eq_single _ 1]
  · simp
  · intro d hd
    rw [coeff_one_pow, hf, smul_eq_mul]
    rcases d with _ | _ | d <;> simp_all

open scoped WithPiTopology in
/-- Over a discrete ring, if `a(0) = 0`, then `f ↦ f ∘ a` is continuous for the topology of
coefficientwise convergence. -/
theorem continuous_subst_of_constantCoeff_zero [TopologicalSpace R] [DiscreteTopology R]
    {a : R⟦X⟧} (ha : a.constantCoeff = 0) : Continuous (fun f : R⟦X⟧ ↦ f.subst a) := by
  obtain rfl := DiscreteTopology.eq_bot (α := R)
  let : UniformSpace R := ⊥
  exact MvPowerSeries.continuous_subst (HasSubst.of_constantCoeff_zero' ha).const

end Subst

/-! ### Coefficients of compositions -/

section Coefficients

/-- If `g(0) = 0`, then the coefficient of `X ^ e` in `g ^ d` vanishes for `e < d`. -/
theorem coeff_pow_eq_zero_of_lt {g : R⟦X⟧} (hg : g.constantCoeff = 0) {d e : ℕ} (h : e < d) :
    (g ^ d).coeff e = 0 := by
  obtain ⟨a, rfl⟩ := X_dvd_iff.mpr hg
  rw [mul_pow]
  exact X_pow_dvd_iff.mp (dvd_mul_right _ _) e h

/-- If `g(0) = 0`, then the coefficient of `X ^ d` in `g ^ d` is `g'(0) ^ d`. -/
theorem coeff_pow_self {g : R⟦X⟧} (hg : g.constantCoeff = 0) (d : ℕ) :
    (g ^ d).coeff d = g.coeff 1 ^ d := by
  obtain ⟨a, rfl⟩ := X_dvd_iff.mpr hg
  simp [mul_pow, coeff_X_pow_mul']

/-- If `g(0) = 0`, then `[X ^ e] (f ∘ g) = ∑_{d ≤ e} [X ^ d] f · [X ^ e] g ^ d`. -/
theorem coeff_subst_eq_sum {g : R⟦X⟧} (hg : g.constantCoeff = 0) (f : R⟦X⟧) (e : ℕ) :
    coeff e (f.subst g) = ∑ d ∈ Finset.range (e + 1), f.coeff d * (g ^ d).coeff e := by
  rw [coeff_subst' (.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  refine finsum_eq_finsetSum_of_support_subset _ fun d hd ↦ Finset.mem_range.mpr ?_
  by_contra h
  exact hd (by simp only [coeff_pow_eq_zero_of_lt hg (show e < d by omega), mul_zero])

/-- If `g(0) = 0` and `X ^ N ∣ g - X`, then `X ^ (N + n) ∣ g ^ (n + 1) - X ^ (n + 1)`. -/
theorem X_pow_dvd_pow_sub_X_pow {g : R⟦X⟧} (hg : g.constantCoeff = 0) {N : ℕ}
    (hN : X ^ N ∣ g - X) (n : ℕ) : X ^ (N + n) ∣ g ^ (n + 1) - X ^ (n + 1) := by
  induction n with
  | zero => simpa using hN
  | succ n ih =>
    have h : g ^ (n + 2) - X ^ (n + 2) = (g ^ (n + 1) - X ^ (n + 1)) * g +
        X ^ (n + 1) * (g - X) := by ring
    rw [h, show N + (n + 1) = N + n + 1 by omega]
    refine dvd_add ?_ ?_
    · rw [pow_succ]
      exact mul_dvd_mul ih (X_dvd_iff.mpr hg)
    · rw [show N + n + 1 = (n + 1) + N by omega, pow_add]
      exact mul_dvd_mul dvd_rfl hN

/-- If `g(0) = 0` and `g ≡ X mod X ^ N`, then
`[X ^ e] (f ∘ g) - [X ^ e] f = f'(0) · [X ^ e] (g - X)` for `1 ≤ e ≤ N`. -/
theorem coeff_subst_sub_coeff_of_dvd_inner {g : R⟦X⟧} (hg : g.constantCoeff = 0) {N : ℕ}
    (hN : X ^ N ∣ g - X) (f : R⟦X⟧) {e : ℕ} (he₁ : 1 ≤ e) (he : e ≤ N) :
    coeff e (f.subst g) - f.coeff e = f.coeff 1 * (g - X).coeff e := by
  have hf : f.coeff e = ∑ d ∈ Finset.range (e + 1), f.coeff d * (X ^ d : R⟦X⟧).coeff e := by
    simp [coeff_X_pow, eq_comm (a := e)]
  rw [coeff_subst_eq_sum hg, hf, ← Finset.sum_sub_distrib, Finset.sum_eq_single 1]
  · rw [pow_one, pow_one, ← mul_sub, ← map_sub]
  · intro d _ hd₁
    obtain rfl | hd₀ := eq_or_ne d 0
    · simp
    · have h := X_pow_dvd_pow_sub_X_pow hg hN (d - 1)
      rw [Nat.sub_add_cancel (by omega)] at h
      rw [← mul_sub, ← map_sub, X_pow_dvd_iff.mp h e (by omega), mul_zero]
  · simp only [Finset.mem_range]
    omega

/-- If `g(0) = 0` and `f ≡ X mod X ^ N`, then
`[X ^ N] (f ∘ g) - [X ^ N] g = [X ^ N] (f - X) · g'(0) ^ N`. -/
theorem coeff_subst_sub_coeff_of_dvd_outer {g : R⟦X⟧} (hg : g.constantCoeff = 0)
    {f : R⟦X⟧} {N : ℕ} (hN : X ^ N ∣ f - X) :
    coeff N (f.subst g) - g.coeff N = (f - X).coeff N * g.coeff 1 ^ N := by
  have hs : HasSubst g := .of_constantCoeff_zero' hg
  have h : coeff N ((f - X).subst g) = (f - X).coeff N * g.coeff 1 ^ N := by
    rw [coeff_subst_eq_sum hg, Finset.sum_eq_single N, coeff_pow_self hg]
    · intro d hd hdN
      rw [X_pow_dvd_iff.mp hN d (by have := Finset.mem_range.mp hd; omega), zero_mul]
    · simp
  rw [← h, subst_sub hs, subst_X hs, map_sub]

end Coefficients

section Iterate

/-- The `n`-fold composition `f^{∘n} = f ∘ ⋯ ∘ f` of a power series with itself, with
`f^{∘0} = X`. -/
noncomputable def iterate (f : R⟦X⟧) (n : ℕ) : R⟦X⟧ :=
  (subst f : R⟦X⟧ → R⟦X⟧)^[n] X

variable {f : R⟦X⟧}

/-- `f^{∘0} = X`. -/
@[simp]
theorem iterate_zero (f : R⟦X⟧) : iterate f 0 = X := rfl

/-- `f^{∘(n + 1)} = f^{∘n} ∘ f`. -/
theorem iterate_succ (f : R⟦X⟧) (n : ℕ) : iterate f (n + 1) = (iterate f n).subst f :=
  Function.iterate_succ_apply' _ _ _

/-- If `f(0)` is nilpotent, then so is `f^{∘n}(0)`. -/
protected theorem HasSubst.iterate (hf : HasSubst f) (n : ℕ) : HasSubst (iterate f n) := by
  induction n with
  | zero => exact HasSubst.X'
  | succ n ih =>
    rw [iterate_succ]
    exact ih.subst hf

/-- `f^{∘1} = f`. -/
theorem iterate_one (hf : HasSubst f) : iterate f 1 = f := by
  rw [iterate_succ, iterate_zero, subst_X hf]

/-- `f^{∘(m + n)} = f^{∘m} ∘ f^{∘n}`. -/
theorem iterate_add (hf : HasSubst f) (m n : ℕ) :
    iterate f (m + n) = (iterate f m).subst (iterate f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, iterate_succ, ih, iterate_succ f n,
      subst_comp_subst_apply (hf.iterate n) hf]

/-- `f^{∘(n + 1)} = f ∘ f^{∘n}`. -/
theorem iterate_succ' (hf : HasSubst f) (n : ℕ) : iterate f (n + 1) = f.subst (iterate f n) := by
  rw [add_comm, iterate_add hf, iterate_one hf]

/-- `f^{∘(m * n)} = (f^{∘m})^{∘n}`. -/
theorem iterate_mul (hf : HasSubst f) (m n : ℕ) :
    iterate f (m * n) = iterate (iterate f m) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, iterate_add hf, ih, iterate_succ]

/-- `g ∘ f^{∘n}` is obtained from `g` by composing with `f` on the right `n` times. -/
theorem subst_iterate (hf : HasSubst f) (n : ℕ) (g : R⟦X⟧) :
    g.subst (iterate f n) = (subst f : R⟦X⟧ → R⟦X⟧)^[n] g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ, ← subst_comp_subst_apply (hf.iterate n) hf, ih,
      Function.iterate_succ_apply']

/-- If `f(0) = 0`, then `f^{∘n}(0) = 0`. -/
theorem constantCoeff_iterate (hf : f.constantCoeff = 0) (n : ℕ) :
    (iterate f n).constantCoeff = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, constantCoeff_subst_of_constantCoeff_zero' hf, ih]

/-- The linear coefficient of `f^{∘n}` is the `n`-th power of the linear coefficient of `f`. -/
theorem coeff_one_iterate (hf : f.constantCoeff = 0) (n : ℕ) :
    (iterate f n).coeff 1 = f.coeff 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, coeff_one_subst hf, ih, pow_succ]

/-- If `f = X + O(X²)`, then `f^{∘n} = X + O(X²)`. -/
theorem two_le_order_iterate_sub_X (hf : f.constantCoeff = 0) (hf' : f.coeff 1 = 1) (n : ℕ) :
    2 ≤ (iterate f n - X).order := by
  refine nat_le_order _ 2 fun i hi ↦ ?_
  rcases i with _ | _ | i
  · simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_iterate hf]
  · simp [coeff_one_iterate hf, hf']
  · omega

/-- If `f(0) = 0` and `f ≡ X mod X ^ N` with `N ≥ 2`, then
`[X ^ e] (f^{∘n} - X) = n · [X ^ e] (f - X)` for `e ≤ N`. -/
theorem coeff_iterate_sub_X (hf : f.constantCoeff = 0) {N : ℕ} (hN₂ : 2 ≤ N)
    (hN : X ^ N ∣ f - X) (n : ℕ) {e : ℕ} (he : e ≤ N) :
    (iterate f n - X).coeff e = (n : R) * (f - X).coeff e := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ]
    obtain rfl | he₀ := eq_or_ne e 0
    · simp [constantCoeff_subst_of_constantCoeff_zero' hf, constantCoeff_iterate hf, hf]
    have hlin : f.coeff 1 = 1 := by
      have h := X_pow_dvd_iff.mp hN 1 (by omega)
      rwa [map_sub, coeff_one_X, sub_eq_zero] at h
    have h := coeff_subst_sub_coeff_of_dvd_inner hf hN (iterate f n) (by omega) he
    rw [coeff_one_iterate hf, hlin, one_pow, one_mul] at h
    have h' := ih he
    rw [map_sub] at h' ⊢
    push_cast
    linear_combination h + h'

/-- `φ(f^{∘n}) = φ(f)^{∘n}` for a ring homomorphism `φ` applied to the coefficients. -/
theorem map_iterate (φ : R →+* S) (hf : HasSubst f) (n : ℕ) :
    (iterate f n).map φ = iterate (f.map φ) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ, iterate_succ, ← ih]
    exact map_subst hf _

end Iterate

section Map

/-- If `f(0) = 0`, then the image of `f` under a ring homomorphism `φ` applied to the
coefficients has constant coefficient `0`. -/
theorem constantCoeff_map_eq_zero (φ : R →+* S) {f : R⟦X⟧} (hf : f.constantCoeff = 0) :
    (f.map φ).constantCoeff = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hf,
    map_zero]

/-- If `f'(0)` is a unit, then so is the linear coefficient of the image of `f` under a ring
homomorphism `φ` applied to the coefficients. -/
theorem isUnit_coeff_one_map (φ : R →+* S) {f : R⟦X⟧} (hf : IsUnit (f.coeff 1)) :
    IsUnit ((f.map φ).coeff 1) := by
  rw [coeff_map]
  exact hf.map φ

end Map

section CompInv

open scoped Classical in
/-- The compositional inverse `w^{∘-1}` of a power series `w` with `w(0) = 0` and invertible
linear coefficient: `w ∘ w^{∘-1} = w^{∘-1} ∘ w = X`. It is `X` if the linear coefficient of `w`
is not a unit. -/
noncomputable def compInv (w : R⟦X⟧) : R⟦X⟧ :=
  if h : IsUnit (w.coeff 1) then w.substInvOfIsUnit h else X

variable {w : R⟦X⟧}

/-- If `w'(0)` is a unit, then `w^{∘-1}` is `PowerSeries.substInvOfIsUnit w`. -/
theorem compInv_eq_substInvOfIsUnit (hw' : IsUnit (w.coeff 1)) :
    w.compInv = w.substInvOfIsUnit hw' :=
  dite_eq_left hw'

/-- If the linear coefficient of `w` is not a unit, then `compInv w = X`. -/
theorem compInv_of_not_isUnit (hw' : ¬IsUnit (w.coeff 1)) : w.compInv = X :=
  dite_eq_right hw'

/-- `w^{∘-1}(0) = 0`. -/
@[simp]
theorem constantCoeff_compInv (w : R⟦X⟧) : w.compInv.constantCoeff = 0 := by
  unfold compInv
  split_ifs <;> simp

/-- `w^{∘-1}` can be substituted, as its constant coefficient is `0`. -/
protected theorem HasSubst.compInv (w : R⟦X⟧) : HasSubst w.compInv :=
  .of_constantCoeff_zero' (constantCoeff_compInv w)

/-- If `w'(0)` is a unit, then the linear coefficient of `w^{∘-1}` is `w'(0)⁻¹`. -/
theorem coeff_one_compInv (hw' : IsUnit (w.coeff 1)) : w.compInv.coeff 1 = hw'.unit⁻¹ := by
  rw [compInv_eq_substInvOfIsUnit hw', coeff_one_substInvOfIsUnit]

/-- If `w'(0)` is a unit, then `w'(0) (w^{∘-1})'(0) = 1`. -/
theorem coeff_one_mul_coeff_one_compInv (hw' : IsUnit (w.coeff 1)) :
    w.coeff 1 * w.compInv.coeff 1 = 1 := by
  rw [coeff_one_compInv hw', hw'.mul_val_inv]

/-- The linear coefficient of `w^{∘-1}` is a unit. -/
theorem isUnit_coeff_one_compInv (w : R⟦X⟧) : IsUnit (w.compInv.coeff 1) := by
  by_cases hw' : IsUnit (w.coeff 1)
  · rw [coeff_one_compInv hw']
    exact Units.isUnit _
  · rw [compInv_of_not_isUnit hw', coeff_one_X]
    exact isUnit_one

/-- `w ∘ w^{∘-1} = X`. -/
theorem subst_compInv_right (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    w.subst w.compInv = X := by
  rw [compInv_eq_substInvOfIsUnit hw', subst_substInvOfIsUnit_right w hw hw']

/-- `w^{∘-1} ∘ w = X`. -/
theorem subst_compInv_left (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    w.compInv.subst w = X := by
  rw [compInv_eq_substInvOfIsUnit hw', subst_substInvOfIsUnit_left w hw hw']

/-- A right compositional inverse of `w` is `w^{∘-1}`. -/
theorem eq_compInv_of_subst_eq_X (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1))
    {v : R⟦X⟧} (hv : HasSubst v) (h : w.subst v = X) : v = w.compInv := by
  rw [compInv_eq_substInvOfIsUnit hw']
  exact eq_substInvOfIsUnit_of_subst_eq_X w hw hw' hv h

/-- `X^{∘-1} = X`. -/
@[simp]
theorem compInv_X : (X : R⟦X⟧).compInv = X :=
  (eq_compInv_of_subst_eq_X constantCoeff_X (by simp) HasSubst.X' (X_subst X)).symm

/-- `(w^{∘-1})^{∘-1} = w`. -/
theorem compInv_compInv (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    w.compInv.compInv = w :=
  (eq_compInv_of_subst_eq_X (constantCoeff_compInv w) (isUnit_coeff_one_compInv w)
    (.of_constantCoeff_zero' hw) (subst_compInv_left hw hw')).symm

/-- `(v ∘ w)^{∘-1} = w^{∘-1} ∘ v^{∘-1}`. -/
theorem compInv_subst {v : R⟦X⟧} (hv : v.constantCoeff = 0) (hv' : IsUnit (v.coeff 1))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    compInv (v.subst w) = w.compInv.subst v.compInv := by
  refine (eq_compInv_of_subst_eq_X (by rwa [constantCoeff_subst_of_constantCoeff_zero' hw])
    (by simpa only [coeff_one_subst hw] using hv'.mul hw')
    ((HasSubst.compInv w).subst (HasSubst.compInv v)) ?_).symm
  rw [← subst_comp_subst_apply (HasSubst.compInv w) (HasSubst.compInv v),
    subst_comp_subst_apply (.of_constantCoeff_zero' hw) (HasSubst.compInv w),
    subst_compInv_right hw hw', X_subst, subst_compInv_right hv hv']

/-- `φ(w^{∘-1}) = φ(w)^{∘-1}` for a ring homomorphism `φ` applied to the coefficients
(Yuan, Lemma 2.1 (3)). -/
theorem map_compInv (φ : R →+* S) (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    w.compInv.map φ = (w.map φ).compInv := by
  refine eq_compInv_of_subst_eq_X (constantCoeff_map_eq_zero φ hw) (isUnit_coeff_one_map φ hw')
    (.of_constantCoeff_zero' (constantCoeff_map_eq_zero φ (constantCoeff_compInv w))) ?_
  refine (map_subst (HasSubst.compInv w) (h := φ) w).symm.trans ?_
  rw [subst_compInv_right hw hw']
  exact map_X φ

end CompInv

section Conj

/-- The conjugate `w ∘ f ∘ w^{∘-1}` of `f` by `w`. Let `w(0) = 0` with invertible linear
coefficient. If a continuous automorphism of `k((T))` over a field `k` sends `T` to `f(T)`, then
it sends `T' = w(T)` to `(conj w f)(T')` (Yuan, Lemma 2.2 (4)). -/
noncomputable def conj (w f : R⟦X⟧) : R⟦X⟧ :=
  subst w.compInv (w.subst f)

variable {v w f g : R⟦X⟧}

/-- If `w(0)` and `f(0)` are nilpotent, then so is `(w ∘ f ∘ w^{∘-1})(0)`. -/
protected theorem HasSubst.conj (hw : HasSubst w) (hf : HasSubst f) : HasSubst (conj w f) :=
  (hw.subst hf).subst (HasSubst.compInv w)

/-- Conjugation by `X` is the identity: `X ∘ f ∘ X^{∘-1} = f`. -/
theorem conj_X (hf : HasSubst f) : conj X f = f := by
  rw [conj, compInv_X, subst_X hf, X_subst]

/-- `w ∘ X ∘ w^{∘-1} = X`. -/
theorem conj_X_right (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) : conj w X = X := by
  rw [conj, X_subst, subst_compInv_right hw hw']

/-- If `w(0) = f(0) = 0`, then `(w ∘ f ∘ w^{∘-1})(0) = 0`. -/
theorem constantCoeff_conj (hw : w.constantCoeff = 0) (hf : f.constantCoeff = 0) :
    (conj w f).constantCoeff = 0 := by
  rw [conj, constantCoeff_subst_of_constantCoeff_zero' (constantCoeff_compInv w),
    constantCoeff_subst_of_constantCoeff_zero' hf, hw]

/-- If `w'(0)` is a unit and `f(0) = 0`, then `w ∘ f ∘ w^{∘-1}` and `f` have the same linear
coefficient. -/
theorem coeff_one_conj (hw' : IsUnit (w.coeff 1)) (hf : f.constantCoeff = 0) :
    (conj w f).coeff 1 = f.coeff 1 := by
  rw [conj, coeff_one_subst (constantCoeff_compInv w), coeff_one_subst hf, mul_right_comm,
    coeff_one_mul_coeff_one_compInv hw', one_mul]

/-- If `w'(0)` and `f'(0)` are units and `f(0) = 0`, then the linear coefficient of
`w ∘ f ∘ w^{∘-1}` is a unit. -/
theorem isUnit_coeff_one_conj (hw' : IsUnit (w.coeff 1)) (hf : f.constantCoeff = 0)
    (hf' : IsUnit (f.coeff 1)) : IsUnit ((conj w f).coeff 1) := by
  rwa [coeff_one_conj hw' hf]

/-- The conjugate intertwines: `(w ∘ f ∘ w^{∘-1}) ∘ w = w ∘ f`. -/
theorem subst_conj (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) :
    (conj w f).subst w = w.subst f := by
  rw [conj, subst_comp_subst_apply (HasSubst.compInv w) (.of_constantCoeff_zero' hw),
    subst_compInv_left hw hw', X_subst]

/-- `w ∘ f ∘ w^{∘-1} = h` if and only if `w ∘ f = h ∘ w`. -/
theorem conj_eq_iff_subst (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) {h : R⟦X⟧} :
    conj w f = h ↔ w.subst f = h.subst w := by
  refine ⟨fun hconj ↦ hconj ▸ (subst_conj hw hw').symm, fun hsubst ↦ ?_⟩
  rw [conj, hsubst, subst_comp_subst_apply (.of_constantCoeff_zero' hw) (HasSubst.compInv w),
    subst_compInv_right hw hw', X_subst]

/-- Conjugation preserves composition: `w ∘ (f ∘ g) ∘ w^{∘-1}` is the composition of
`w ∘ f ∘ w^{∘-1}` and `w ∘ g ∘ w^{∘-1}`. -/
theorem conj_subst (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) (hf : HasSubst f)
    (hg : HasSubst g) : conj w (f.subst g) = (conj w f).subst (conj w g) := by
  have hw₀ : HasSubst w := .of_constantCoeff_zero' hw
  rw [conj_eq_iff_subst hw hw', subst_comp_subst_apply (hw₀.conj hg) hw₀, subst_conj hw hw',
    ← subst_comp_subst_apply hw₀ hg, subst_conj hw hw', subst_comp_subst_apply hf hg]

/-- Conjugation preserves iterates: `w ∘ f^{∘n} ∘ w^{∘-1} = (w ∘ f ∘ w^{∘-1})^{∘n}`. -/
theorem conj_iterate (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) (hf : HasSubst f)
    (n : ℕ) : conj w (iterate f n) = iterate (conj w f) n := by
  induction n with
  | zero => exact conj_X_right hw hw'
  | succ n ih => rw [iterate_succ, conj_subst hw hw' (hf.iterate n) hf, ih, iterate_succ]

/-- Conjugating by `w` and then by `v` is conjugating by `v ∘ w`. -/
theorem conj_conj (hv : v.constantCoeff = 0) (hv' : IsUnit (v.coeff 1))
    (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1)) (hf : HasSubst f) :
    conj v (conj w f) = conj (v.subst w) f := by
  have hv₀ : HasSubst v := .of_constantCoeff_zero' hv
  have hw₀ : HasSubst w := .of_constantCoeff_zero' hw
  refine ((conj_eq_iff_subst (by rwa [constantCoeff_subst_of_constantCoeff_zero' hw])
    (by simpa only [coeff_one_subst hw] using hv'.mul hw')).mpr ?_).symm
  rw [← subst_comp_subst_apply hv₀ hw₀, subst_conj hv hv',
    subst_comp_subst_apply (hw₀.conj hf) hw₀, subst_conj hw hw',
    ← subst_comp_subst_apply hw₀ hf]

/-- Conjugating by `w` and then by `w^{∘-1}` is the identity. -/
theorem conj_compInv_conj (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1))
    (hf : HasSubst f) : conj w.compInv (conj w f) = f := by
  rw [conj_conj (constantCoeff_compInv w) (isUnit_coeff_one_compInv w) hw hw' hf,
    subst_compInv_left hw hw', conj_X hf]

/-- Conjugating by `w^{∘-1}` and then by `w` is the identity. -/
theorem conj_conj_compInv (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1))
    (hf : HasSubst f) : conj w (conj w.compInv f) = f := by
  rw [conj_conj hw hw' (constantCoeff_compInv w) (isUnit_coeff_one_compInv w) hf,
    subst_compInv_right hw hw', conj_X hf]

/-- `φ(w ∘ f ∘ w^{∘-1}) = φ(w) ∘ φ(f) ∘ φ(w)^{∘-1}` for a ring homomorphism `φ` applied to the
coefficients. -/
theorem map_conj (φ : R →+* S) (hw : w.constantCoeff = 0) (hw' : IsUnit (w.coeff 1))
    (hf : HasSubst f) : (conj w f).map φ = conj (w.map φ) (f.map φ) := by
  rw [conj, conj, ← map_compInv φ hw hw']
  refine (map_subst (HasSubst.compInv w) _).trans ?_
  congr 1
  exact map_subst hf w

end Conj

end PowerSeries
