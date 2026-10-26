/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Substitution
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Taylor expansion of substitutions close to the identity

Let `R` be a local Artinian ring with principal maximal ideal, and let `g ∈ R((T))` satisfy
`g = T + O(T ^ (d + 1))` with `d ≥ 1`. For every integer `m` and every `f = O(T ^ m)`, the
substitution `f ↦ f(g)` satisfies `f(g) - f = O(T ^ (m + d))` and
`f(g) = f + (g - T) f' + O(T ^ (m + 2 d))`. If `g = T + α T ^ (d + 1) + O(T ^ (d + 2))` and
`x = b T ^ m + O(T ^ (m + 1))`, then `x(g) - x = m α b T ^ (m + d) + O(T ^ (m + d + 1))`. For a
power series `U` the bounds improve to `U(g) - U = O(T ^ (d + 1))` and
`U(g) - U - (g - T) U' = O(T ^ (2 d + 2))`. Over a field the latter remainder is `(g - T) ^ 2`
times a power series, so `v_T(U(g) - U) = v_T(g - T) + v_T(U')` whenever `U' ≠ 0` and
`v_T(U') < v_T(g - T)`.

If `σ` is an automorphism of a field of norms with residue field `𝔽_q` and `g = f_σ` is its series
in a uniformizer `T`, then `x(g) = σ x` (Yuan, Lemma 2.2 (2)), and `g = T + O(T ^ (d + 1))` means
that `σ` has ramification number at least `d`. In this setting the results above are Yuan,
Lemma 3.2, and the expansions in the proofs of Yuan, Proposition 3.1 and Lemma 4.2.

## Main results

* `LaurentSeries.subst_sub_mem_orderAddSubgroup`: `f(g) - f = O(T ^ (m + d))` (Yuan, Lemma 3.2).
* `LaurentSeries.subst_sub_leadingTerm_mem`: `x(g) - x = m α b T ^ (m + d) + O(T ^ (m + d + 1))`
  (Yuan, Lemma 3.2).
* `LaurentSeries.subst_taylor_mem_orderAddSubgroup`: `f(g) - f - (g - T) f' = O(T ^ (m + 2 d))`,
  the expansion in the proof of Yuan, Proposition 3.1.
* `LaurentSeries.subst_ofPowerSeries_sub_mem`, `LaurentSeries.subst_ofPowerSeries_taylor_mem`:
  `U(g) - U = O(T ^ (d + 1))` and `U(g) - U - (g - T) U' = O(T ^ (2 d + 2))` for a power series
  `U` (Yuan, proof of Lemma 4.2).
* `LaurentSeries.exists_powerSeries_taylor_remainder`: over a field,
  `U(g) - U - (g - T) U' ∈ (g - T) ^ 2 k⟦T⟧`.
* `LaurentSeries.order_subst_ofPowerSeries_sub_eq`: `v_T(U(g) - U) = v_T(g - T) + v_T(U')` when
  `v_T(U') < v_T(g - T)`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 3.2, proof of Proposition 3.1 and proof of Lemma 4.2.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

open Filter
open scoped LaurentSeries.OrderTopology

section CommRing

variable {R : Type*} [CommRing R]

private theorem sub_one_sq_dvd_zpow_sub_one_sub_mul (u : Rˣ) (j : ℤ) :
    ((u : R) - 1) ^ 2 ∣ ((u ^ j : Rˣ) : R) - 1 - (j : R) * ((u : R) - 1) := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n _ =>
    have hpos : ((u : R) - 1) ^ 2 ∣
        (u : R) ^ (n + 1) - 1 - ((n + 1 : ℕ) : R) * ((u : R) - 1) := by
      exact (sq_dvd_add_pow_sub_sub ((u : R) - 1) 1 (n + 1)).trans (dvd_of_eq (by ring))
    change ((u : R) - 1) ^ 2 ∣
      ((u ^ ((n + 1 : ℕ) : ℤ) : Rˣ) : R) - 1 - (((n + 1 : ℕ) : ℤ) : R) * ((u : R) - 1)
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast] using hpos
  | pred n ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨((u⁻¹ : Rˣ) : R) * (v - ((-(n : ℤ) - 1 : ℤ) : R)), ?_⟩
    rw [zpow_sub_one, Units.val_mul]
    push_cast
    have hunit : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    push_cast at hv
    linear_combination ((u⁻¹ : Rˣ) : R) * hv +
      (1 + ((-(n : R) - 1) * ((u : R) - 1))) * hunit

private theorem ne_zero_and_order_eq_of_orderTop_eq {f : LaurentSeries R} {m : ℤ}
    (hf : f.orderTop = (m : WithTop ℤ)) : f ≠ 0 ∧ f.order = m := by
  have hne : f ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [hf]; exact WithTop.coe_ne_top)
  exact ⟨hne, by exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero hne).trans hf⟩

/-- A series `g = T + O(T ^ (d + 1))` with `d ≥ 1` is `T u` for a unit `u = 1 + O(T ^ d)`. -/
private theorem exists_eq_X_mul_ofPowerSeries {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) :
    ∃ u : (PowerSeries R)ˣ,
      g = HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R) ∧
        HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) ∈ orderAddSubgroup d := by
  let z := HahnSeries.single (-1 : ℤ) 1 * (g - HahnSeries.single (1 : ℤ) 1)
  have hz : z ∈ orderAddSubgroup d := by
    simpa only [show (-1 : ℤ) + (d + 1) = d by omega] using
      mul_mem_orderAddSubgroup
        (show (HahnSeries.single (-1 : ℤ) 1 : LaurentSeries R) ∈ orderAddSubgroup (-1) from
          HahnSeries.orderTop_single_le) hg
  let Z := PowerSeries.mk fun n : ℕ ↦ z.coeff n
  have hZ : HahnSeries.ofPowerSeries ℤ R Z = z :=
    ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero z
      (orderAddSubgroup_antitone (show 0 ≤ d by omega) hz)
  have hZ0 : Z.constantCoeff = 0 := by
    simpa only [Z, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      Nat.cast_zero] using (mem_orderAddSubgroup_iff_coeff d z).mp hz 0 (by omega)
  have hU : IsUnit (1 + Z) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [map_add, map_one, hZ0, add_zero]; simp)
  refine ⟨hU.unit, ?_, ?_⟩
  · simp only [hU.unit_spec, map_add, map_one, hZ]
    have hT : (HahnSeries.single (1 : ℤ) 1 : LaurentSeries R) *
        HahnSeries.single (-1 : ℤ) 1 = 1 := by simp
    dsimp only [z]
    linear_combination -(g - HahnSeries.single (1 : ℤ) 1) * hT
  · simpa only [hU.unit_spec, add_sub_cancel_left, hZ] using hz

end CommRing

section IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- `T u` is admissible for every unit `u` of `R⟦T⟧`. -/
theorem isAdmissible_X_mul_ofPowerSeries (u : (PowerSeries R)ˣ) :
    IsAdmissible
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R)) := by
  have hlinear : IsUnit ((PowerSeries.X * (u : PowerSeries R)).coeff 1) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact u.isUnit.map PowerSeries.constantCoeff
  simpa only [map_mul, HahnSeries.ofPowerSeries_X] using
    isAdmissible_ofPowerSeries (by simp) hlinear

/-- A series `g = T + O(T ^ 2)` is admissible. -/
theorem isAdmissible_of_sub_X_mem {g : LaurentSeries R}
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup 2) : IsAdmissible g := by
  obtain ⟨u, rfl, -⟩ := exists_eq_X_mul_ofPowerSeries (d := 1) le_rfl hg
  exact isAdmissible_X_mul_ofPowerSeries u

end IsLocalRing

section Subst

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsArtinianRing R] [IsPrincipalIdealRing R]

/-- Substitution of `T u`, for a unit `u` of `R⟦T⟧`, sends `b T ^ j` to `b T ^ j u ^ j` for every
`j ∈ ℤ`. -/
theorem subst_X_mul_ofPowerSeries_single (u : (PowerSeries R)ˣ) (j : ℤ) (b : R) :
    subst (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R))
        (HahnSeries.single j b) =
      HahnSeries.single j b *
        HahnSeries.ofPowerSeries ℤ R ((u ^ j : (PowerSeries R)ˣ) : PowerSeries R) := by
  let F := subst (HahnSeries.single (1 : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R))
  have hX : F (HahnSeries.single (1 : ℤ) 1) =
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R) :=
    subst_X (isAdmissible_X_mul_ofPowerSeries u)
  have hneg : F (HahnSeries.single (-1 : ℤ) 1) = HahnSeries.single (-1 : ℤ) 1 *
      HahnSeries.ofPowerSeries ℤ R ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) := by
    refine left_inv_eq_right_inv (a := F (HahnSeries.single (1 : ℤ) 1)) ?_ ?_
    · rw [← map_mul]
      simp
    · rw [hX]
      calc
        _ = (HahnSeries.single (1 : ℤ) 1 * HahnSeries.single (-1 : ℤ) 1) *
            HahnSeries.ofPowerSeries ℤ R
              ((u : PowerSeries R) * ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)) := by
          rw [map_mul]
          ring
        _ = 1 := by simp
  have hone (j : ℤ) : F (HahnSeries.single j 1) = HahnSeries.single j 1 *
      HahnSeries.ofPowerSeries ℤ R ((u ^ j : (PowerSeries R)ˣ) : PowerSeries R) := by
    induction j using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [show (HahnSeries.single ((n : ℤ) + 1) 1 : LaurentSeries R) =
          HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 by simp,
        map_mul, ih, hX, zpow_add, zpow_one, Units.val_mul, map_mul]
      ring
    | pred n ih =>
      rw [show (HahnSeries.single (-(n : ℤ) - 1) 1 : LaurentSeries R) =
          HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.single (-1 : ℤ) 1 by
            simp [sub_eq_add_neg],
        map_mul, ih, hneg, zpow_sub_one, Units.val_mul, map_mul]
      ring
  have hC : F (HahnSeries.C b) = HahnSeries.C b := subst_C _ b
  have hb : (HahnSeries.single j b : LaurentSeries R) =
      HahnSeries.C b * HahnSeries.single j 1 := by simp
  change F (HahnSeries.single j b) = _
  rw [hb, map_mul, hC, hone]
  ring

private theorem subst_X_mul_single_taylor_mem (u : (PowerSeries R)ˣ) {d : ℤ}
    (hd : HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) ∈ orderAddSubgroup d)
    (j : ℤ) (b : R) :
    subst (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R))
          (HahnSeries.single j b) - HahnSeries.single j b -
        HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) *
          derivative R (HahnSeries.single j b) ∈ orderAddSubgroup (j + 2 * d) := by
  have hcast : (j : LaurentSeries R) = HahnSeries.C (j : R) :=
    (map_intCast (HahnSeries.C : R →+* LaurentSeries R) j).symm
  have hlin : (HahnSeries.single (1 : ℤ) 1 : LaurentSeries R) *
      derivative R (HahnSeries.single j b) = HahnSeries.single j b * (j : LaurentSeries R) := by
    simp only [derivative_single, hcast, HahnSeries.C_apply, HahnSeries.single_mul_single,
      show (1 : ℤ) + (j - 1) = j by omega, mul_one, add_zero, mul_comm]
  have heq : subst (HahnSeries.single (1 : ℤ) 1 *
          HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R)) (HahnSeries.single j b) -
        HahnSeries.single j b -
        HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) *
          derivative R (HahnSeries.single j b) =
      HahnSeries.single j b * HahnSeries.ofPowerSeries ℤ R
        (((u ^ j : (PowerSeries R)ˣ) : PowerSeries R) - 1 -
          (j : PowerSeries R) * ((u : PowerSeries R) - 1)) := by
    rw [subst_X_mul_ofPowerSeries_single u j b]
    simp only [map_sub, map_one, map_mul, map_intCast]
    linear_combination -(HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R) - 1) * hlin
  obtain ⟨V, hV⟩ := sub_one_sq_dvd_zpow_sub_one_sub_mul u j
  rw [heq, hV, map_mul, map_pow, pow_two]
  have hfactor := mul_mem_orderAddSubgroup (mul_mem_orderAddSubgroup hd hd)
    (ofPowerSeries_mem_orderAddSubgroup_zero V)
  simpa only [add_zero, ← two_mul] using mul_mem_orderAddSubgroup
    (show HahnSeries.single j b ∈ orderAddSubgroup j from HahnSeries.orderTop_single_le) hfactor

private theorem subst_X_mul_taylor_mem (u : (PowerSeries R)ˣ) {d : ℤ}
    (hd : HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) ∈ orderAddSubgroup d)
    {m : ℤ} {f : LaurentSeries R} (hf : f ∈ orderAddSubgroup m) :
    subst (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R)) f -
        f - HahnSeries.single (1 : ℤ) 1 *
          HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) * derivative R f ∈
      orderAddSubgroup (m + 2 * d) := by
  let F := subst (HahnSeries.single (1 : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R))
  let δ := HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1)
  have hfinite (n : ℕ) : F (HahnSeries.truncLT (n : ℤ) f) - HahnSeries.truncLT (n : ℤ) f -
      δ * derivative R (HahnSeries.truncLT (n : ℤ) f) ∈ orderAddSubgroup (m + 2 * d) := by
    classical
    rw [truncLT_eq_sum_Ico, map_sum, map_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine sum_mem fun j _ ↦ ?_
    by_cases hj : m ≤ j
    · exact orderAddSubgroup_antitone (by omega)
        (subst_X_mul_single_taylor_mem u hd j (f.coeff j))
    · have hz := (mem_orderAddSubgroup_iff_coeff m f).mp hf j (lt_of_not_ge hj)
      simp only [hz, map_zero, sub_self, mul_zero, zero_mem]
  have hc : Continuous fun x : LaurentSeries R ↦ F x - x - δ * derivative R x :=
    ((continuous_subst _).sub continuous_id).sub (continuous_const.mul continuous_derivative)
  exact (isClosed_orderAddSubgroup (m + 2 * d)).mem_of_tendsto
    ((hc.tendsto f).comp (tendsto_truncLT_orderTopology f)) (Eventually.of_forall hfinite)

/-- First-order Taylor expansion: for `g = T + O(T ^ (d + 1))` with `d ≥ 1` and every
`f = O(T ^ m)`, `m ∈ ℤ`, one has `f(g) - f - (g - T) f' = O(T ^ (m + 2 d))`. -/
theorem subst_taylor_mem_orderAddSubgroup {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) {m : ℤ}
    {f : LaurentSeries R} (hf : f ∈ orderAddSubgroup m) :
    subst g f - f - (g - HahnSeries.single (1 : ℤ) 1) * derivative R f ∈
      orderAddSubgroup (m + 2 * d) := by
  obtain ⟨u, rfl, hu⟩ := exists_eq_X_mul_ofPowerSeries hd hg
  have hδ : HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R (u : PowerSeries R) -
      HahnSeries.single (1 : ℤ) 1 =
        HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ R ((u : PowerSeries R) - 1) := by
    simp only [map_sub, map_one]
    ring
  rw [hδ]
  exact subst_X_mul_taylor_mem u hu hf

/-- For `g = T + O(T ^ (d + 1))` with `d ≥ 1` and every `f = O(T ^ m)`, `m ∈ ℤ`, one has
`f(g) - f = O(T ^ (m + d))` (Yuan, Lemma 3.2). -/
theorem subst_sub_mem_orderAddSubgroup {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) {m : ℤ}
    {f : LaurentSeries R} (hf : f ∈ orderAddSubgroup m) :
    subst g f - f ∈ orderAddSubgroup (m + d) := by
  have hlin : (g - HahnSeries.single (1 : ℤ) 1) * derivative R f ∈ orderAddSubgroup (m + d) := by
    simpa only [show d + 1 + (m - 1) = m + d by omega] using
      mul_mem_orderAddSubgroup hg (derivative_mem_orderAddSubgroup m f hf)
  simpa only [sub_add_cancel] using
    add_mem (orderAddSubgroup_antitone (show m + d ≤ m + 2 * d by omega)
      (subst_taylor_mem_orderAddSubgroup hd hg hf)) hlin

/-- For `g = T + α T ^ (d + 1) + O(T ^ (d + 2))` with `d ≥ 1` and `x = b T ^ m + O(T ^ (m + 1))`,
`m ∈ ℤ`, one has `x(g) - x = m α b T ^ (m + d) + O(T ^ (m + d + 1))` (Yuan, Lemma 3.2). -/
theorem subst_sub_leadingTerm_mem {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d) {α : R}
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈
      orderAddSubgroup (d + 2))
    {x : LaurentSeries R} {m : ℤ} {b : R}
    (hx : x - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) :
    subst g x - x - HahnSeries.single (m + d) ((m : R) * α * b) ∈
      orderAddSubgroup (m + d + 1) := by
  let δ := g - HahnSeries.single (1 : ℤ) 1
  have hδ : δ ∈ orderAddSubgroup (d + 1) := mem_orderAddSubgroup_of_sub_single_mem (b := α)
    (by simpa only [show d + 1 + 1 = d + 2 by omega] using hg)
  have hTaylor : subst g x - x - δ * derivative R x ∈ orderAddSubgroup (m + d + 1) :=
    orderAddSubgroup_antitone (by omega)
      (subst_taylor_mem_orderAddSubgroup hd hδ (mem_orderAddSubgroup_of_sub_single_mem hx))
  have hDx : derivative R x - derivative R (HahnSeries.single m b) ∈ orderAddSubgroup m := by
    simpa only [map_sub, add_sub_cancel_right] using
      derivative_mem_orderAddSubgroup (m + 1) (x - HahnSeries.single m b) hx
  have hfirst : δ * (derivative R x - derivative R (HahnSeries.single m b)) ∈
      orderAddSubgroup (m + d + 1) := by
    simpa only [show d + 1 + m = m + d + 1 by omega] using mul_mem_orderAddSubgroup hδ hDx
  have hsecond : (δ - HahnSeries.single (d + 1) α) * derivative R (HahnSeries.single m b) ∈
      orderAddSubgroup (m + d + 1) := by
    have hDm := derivative_mem_orderAddSubgroup m (HahnSeries.single m b)
      (show HahnSeries.single m b ∈ orderAddSubgroup m from HahnSeries.orderTop_single_le)
    simpa only [show d + 2 + (m - 1) = m + d + 1 by omega] using mul_mem_orderAddSubgroup hg hDm
  have hlead : HahnSeries.single (d + 1) α * derivative R (HahnSeries.single m b) =
      HahnSeries.single (m + d) ((m : R) * α * b) := by
    rw [derivative_single, HahnSeries.single_mul_single, show d + 1 + (m - 1) = m + d by omega]
    congr 1
    ring
  have heq : subst g x - x - HahnSeries.single (m + d) ((m : R) * α * b) =
      (subst g x - x - δ * derivative R x) +
        (δ * (derivative R x - derivative R (HahnSeries.single m b)) +
          (δ - HahnSeries.single (d + 1) α) * derivative R (HahnSeries.single m b)) := by
    rw [← hlead]
    ring
  rw [heq]
  exact add_mem hTaylor (add_mem hfirst hsecond)

/-- For `g = T + O(T ^ (d + 1))` with `d ≥ 1` and a power series `U`,
`U(g) - U = O(T ^ (d + 1))` (Yuan, proof of Lemma 4.2). -/
theorem subst_ofPowerSeries_sub_mem {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) (U : PowerSeries R) :
    subst g (HahnSeries.ofPowerSeries ℤ R U) - HahnSeries.ofPowerSeries ℤ R U ∈
      orderAddSubgroup (d + 1) := by
  have hx : HahnSeries.ofPowerSeries ℤ R U - HahnSeries.C U.constantCoeff ∈
      orderAddSubgroup 1 := by
    rw [mem_orderAddSubgroup_iff_coeff]
    intro j hj
    rw [HahnSeries.coeff_sub, HahnSeries.C_apply]
    by_cases hj0 : j < 0
    · rw [PowerSeries.coeff_coe, ite_eq_left hj0, HahnSeries.coeff_single_of_ne (ne_of_lt hj0),
        sub_self]
    · obtain rfl : j = 0 := by omega
      simp only [show (0 : ℤ) = (0 : ℕ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, HahnSeries.coeff_single_same, sub_self]
  simpa only [map_sub, subst_C, sub_sub_sub_cancel_right, add_comm 1 d] using
    subst_sub_mem_orderAddSubgroup hd hg hx

/-- For `g = T + O(T ^ (d + 1))` with `d ≥ 1` and a power series `U`,
`U(g) - U - (g - T) U' = O(T ^ (2 d + 2))`. -/
theorem subst_ofPowerSeries_taylor_mem {g : LaurentSeries R} {d : ℤ} (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) (U : PowerSeries R) :
    subst g (HahnSeries.ofPowerSeries ℤ R U) - HahnSeries.ofPowerSeries ℤ R U -
        (g - HahnSeries.single (1 : ℤ) 1) * derivative R (HahnSeries.ofPowerSeries ℤ R U) ∈
      orderAddSubgroup (2 * d + 2) := by
  let x := HahnSeries.ofPowerSeries ℤ R U - HahnSeries.C U.constantCoeff -
    HahnSeries.single (1 : ℤ) (U.coeff 1)
  have hx : x ∈ orderAddSubgroup 2 := by
    rw [mem_orderAddSubgroup_iff_coeff]
    intro j hj
    dsimp only [x]
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.C_apply]
    by_cases hj0 : j < 0
    · rw [PowerSeries.coeff_coe, ite_eq_left hj0, HahnSeries.coeff_single_of_ne (ne_of_lt hj0),
        HahnSeries.coeff_single_of_ne (by omega : j ≠ 1), sub_self, sub_self]
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · simp [PowerSeries.coeff_coe]
      · simp [PowerSeries.coeff_coe]
  have hrep : (HahnSeries.single (1 : ℤ) (U.coeff 1) : LaurentSeries R) =
      HahnSeries.C (U.coeff 1) * HahnSeries.single (1 : ℤ) 1 := by simp
  have hlinear : subst g (HahnSeries.single (1 : ℤ) (U.coeff 1)) =
      HahnSeries.C (U.coeff 1) * g := by
    rw [hrep, map_mul, subst_C, subst_X (isAdmissible_of_sub_X_mem
      (orderAddSubgroup_antitone (show (2 : ℤ) ≤ d + 1 by omega) hg))]
  have heq : subst g x - x - (g - HahnSeries.single (1 : ℤ) 1) * derivative R x =
      subst g (HahnSeries.ofPowerSeries ℤ R U) - HahnSeries.ofPowerSeries ℤ R U -
        (g - HahnSeries.single (1 : ℤ) 1) * derivative R (HahnSeries.ofPowerSeries ℤ R U) := by
    dsimp only [x]
    simp only [map_sub]
    rw [subst_C, hlinear, derivative_C, derivative_single, hrep]
    simp only [sub_self, Int.cast_one, one_mul, HahnSeries.C_apply]
    ring
  simpa only [heq, add_comm 2 (2 * d)] using subst_taylor_mem_orderAddSubgroup hd hg hx

end Subst

section Field

variable {k : Type*} [Field k]

/-- For `g = T + O(T ^ 2)` and a power series `U` over a field, `U(g) - U - (g - T) U'` is
`(g - T) ^ 2` times a power series. -/
theorem exists_powerSeries_taylor_remainder {g : LaurentSeries k}
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup 2) (U : PowerSeries k) :
    ∃ V : PowerSeries k,
      subst g (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U -
          (g - HahnSeries.single (1 : ℤ) 1) *
            HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U) =
        (g - HahnSeries.single (1 : ℤ) 1) ^ 2 * HahnSeries.ofPowerSeries ℤ k V := by
  by_cases hδ : g - HahnSeries.single (1 : ℤ) 1 = 0
  · refine ⟨0, ?_⟩
    rw [hδ, sub_eq_zero.mp hδ, subst_X_left_apply]
    ring
  let δ := g - HahnSeries.single (1 : ℤ) 1
  replace hδ : δ ≠ 0 := hδ
  have hδtop : (δ.order : WithTop ℤ) = δ.orderTop := HahnSeries.order_eq_orderTop_of_ne_zero hδ
  have h2 : 2 ≤ δ.order := by
    have h : ((2 : ℤ) : WithTop ℤ) ≤ δ.orderTop := hg
    rw [← hδtop] at h
    exact_mod_cast h
  let A := subst g (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U -
    δ * HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)
  have hA : A ∈ orderAddSubgroup (2 * δ.order) := by
    have h := subst_ofPowerSeries_taylor_mem (d := δ.order - 1) (by omega)
      (show δ ∈ orderAddSubgroup (δ.order - 1 + 1) by
        rw [sub_add_cancel]
        exact mem_orderAddSubgroup_order δ) U
    simpa only [derivative_ofPowerSeries, show 2 * (δ.order - 1) + 2 = 2 * δ.order by ring]
      using h
  let q := A / δ ^ 2
  have hprod : δ ^ 2 * q = A := mul_div_cancel₀ A (pow_ne_zero 2 hδ)
  have hq : q ∈ orderAddSubgroup 0 := by
    by_cases hq0 : q = 0
    · simp only [hq0, zero_mem]
    have hAne : A ≠ 0 := fun h ↦ mul_ne_zero (pow_ne_zero 2 hδ) hq0 (hprod.trans h)
    have hAorder : 2 * δ.order ≤ A.order := by
      have h : ((2 * δ.order : ℤ) : WithTop ℤ) ≤ A.orderTop := hA
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hAne] at h
      exact_mod_cast h
    have ho := congrArg HahnSeries.order hprod
    rw [HahnSeries.order_mul (pow_ne_zero 2 hδ) hq0, pow_two, HahnSeries.order_mul hδ hδ] at ho
    exact orderAddSubgroup_antitone (show 0 ≤ q.order by omega) (mem_orderAddSubgroup_order q)
  refine ⟨PowerSeries.mk fun n : ℕ ↦ q.coeff n, ?_⟩
  rw [ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero q hq]
  exact hprod.symm

/-- For `g` with `v(g - T) = d + 1`, `d ≥ 1`, and a power series `U` over a field with
`U' ≠ 0` and `v(U') < d + 1`, one has `v(U(g) - U) = d + 1 + v(U')`. -/
theorem order_subst_ofPowerSeries_sub_eq {g : LaurentSeries k} {d : ℤ} (hd : 1 ≤ d)
    (hg : (g - HahnSeries.single (1 : ℤ) 1).orderTop = ((d + 1 : ℤ) : WithTop ℤ))
    (U : PowerSeries k) (hU : HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U) ≠ 0)
    (hsmall : (HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)).order < d + 1) :
    (subst g (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U).order =
      d + 1 + (HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)).order := by
  let δ := g - HahnSeries.single (1 : ℤ) 1
  let D := HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)
  change D.order < d + 1 at hsmall
  let B := subst g (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U
  obtain ⟨V, hV⟩ := exists_powerSeries_taylor_remainder
    (orderAddSubgroup_antitone (show (2 : ℤ) ≤ d + 1 by omega) hg.ge) U
  change B - δ * D = δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V at hV
  have hB : B = δ * D + δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V := by linear_combination hV
  obtain ⟨hδne, hδorder⟩ := ne_zero_and_order_eq_of_orderTop_eq hg
  have hLne : δ * D ≠ 0 := mul_ne_zero hδne hU
  have hLorder : (δ * D).order = d + 1 + D.order := by
    rw [HahnSeries.order_mul hδne hU, hδorder]
  have hR : δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V ∈ orderAddSubgroup (2 * d + 2) := by
    simpa only [pow_two, add_zero, show d + 1 + (d + 1) = 2 * d + 2 by omega] using
      mul_mem_orderAddSubgroup (mul_mem_orderAddSubgroup hg.ge hg.ge)
        (ofPowerSeries_mem_orderAddSubgroup_zero V)
  have hlt : (δ * D).orderTop < (δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V).orderTop := by
    calc
      (δ * D).orderTop = ((d + 1 + D.order : ℤ) : WithTop ℤ) := by
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hLne, hLorder]
      _ < ((2 * d + 2 : ℤ) : WithTop ℤ) := by
        exact_mod_cast (by omega : d + 1 + D.order < 2 * d + 2)
      _ ≤ _ := hR
  have hBtop : B.orderTop = ((d + 1 + D.order : ℤ) : WithTop ℤ) := by
    rw [hB, HahnSeries.orderTop_add_eq_left hlt,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hLne, hLorder]
  exact (ne_zero_and_order_eq_of_orderTop_eq hBtop).2

end Field

end LaurentSeries
