module

public import FalseTateNonliftability.LaurentSeries.TruncationDensity
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Continuous Laurent differentiation and the evaluation chain rule

The function throughout is Mathlib's canonical `LaurentSeries.derivative`.
Its coefficient formula gives continuity in the named order topology.
Finite monomial identities then extend to all Laurent series by actual
truncation limits, over arbitrary commutative coefficient rings.

This proves blueprint lemmas `nl:laurent-derivative-continuity` and
`nl:laurent-evaluation-chain-rule`.
-/

@[expose] public section

namespace LaurentSeries

open Filter
open scoped Topology

noncomputable section

variable {R : Type*} [CommRing R]

/-- The coefficient formula for canonical differentiation over any
commutative coefficient ring. -/
theorem coeff_derivative (f : LaurentSeries R) (j : ℤ) :
    (derivative R f).coeff j = ((j + 1 : ℤ) : R) * f.coeff (j + 1) := by
  simp [derivative, hasseDeriv_coeff, zsmul_eq_mul]

@[simp]
theorem derivative_single (j : ℤ) (b : R) :
    derivative R (HahnSeries.single j b) = HahnSeries.single (j - 1) ((j : R) * b) := by
  simp [derivative, hasseDeriv_single, zsmul_eq_mul]

@[simp]
theorem derivative_C (b : R) : derivative R (HahnSeries.C b) = 0 := by
  rw [HahnSeries.C_apply, derivative_single]
  simp

/-- The canonical Laurent derivative restricts to the canonical power-series derivative. -/
theorem derivative_ofPowerSeries (H : PowerSeries R) :
    derivative R (HahnSeries.ofPowerSeries ℤ R H) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.derivative H) := by
  ext j
  rw [coeff_derivative]
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, show ((n : ℤ) + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by omega,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_derivative]
    push_cast
    exact mul_comm _ _
  | negSucc n =>
    cases n with
    | zero => simp [PowerSeries.coeff_coe]
    | succ n =>
      rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe,
        ite_eq_left (by omega), ite_eq_left (by omega), mul_zero]

/-- A power-series coordinate with unit linear coefficient has a unit actual
Laurent derivative over an arbitrary commutative coefficient ring. -/
theorem isUnit_derivative_ofPowerSeries (H : PowerSeries R) (hlinear : IsUnit (H.coeff 1)) :
    IsUnit (derivative R (HahnSeries.ofPowerSeries ℤ R H)) := by
  rw [derivative_ofPowerSeries]
  apply IsUnit.map (HahnSeries.ofPowerSeries ℤ R)
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_derivative, zero_add, Nat.cast_zero, Nat.cast_one, mul_one] using hlinear

/-- Differentiation loses at most one degree of a lower support bound. -/
theorem derivative_mem_orderAddSubgroup (m : ℤ) (f : LaurentSeries R)
    (hf : f ∈ orderAddSubgroup m) : derivative R f ∈ orderAddSubgroup (m - 1) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [coeff_derivative, (mem_orderAddSubgroup_iff_coeff m f).mp hf (j + 1) (by omega), mul_zero]

/-- The canonical derivative is continuous in the explicitly named order topology. -/
theorem continuous_derivative :
    @Continuous (LaurentSeries R) (LaurentSeries R) (orderTopology R) (orderTopology R)
      (derivative R) := by
  let := orderTopology R
  rw [continuous_iff_continuousAt]
  intro f
  change Tendsto (derivative R) (nhds f) (nhds (derivative R f))
  rw [(orderTopology_hasBasis_nhds f).tendsto_iff
    (orderTopology_hasBasis_nhds (derivative R f))]
  intro m _
  refine ⟨m + 1, trivial, ?_⟩
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rw [← map_sub]
  simpa only [add_sub_cancel_right] using derivative_mem_orderAddSubgroup (m + 1) (g - f) hg

private theorem derivative_single_mul_single (i j : ℤ) (b c : R) :
    derivative R (HahnSeries.single i b * HahnSeries.single j c) =
      derivative R (HahnSeries.single i b) * HahnSeries.single j c +
        HahnSeries.single i b * derivative R (HahnSeries.single j c) := by
  simp only [HahnSeries.single_mul_single, derivative_single]
  have hi : (i - 1) + j = i + j - 1 := by omega
  have hj : i + (j - 1) = i + j - 1 := by omega
  rw [hi, hj, ← HahnSeries.single_add]
  congr 1
  push_cast
  ring

private theorem derivative_finite_sums_mul (s t : Finset ℤ) (b c : ℤ → R) :
    derivative R ((∑ i ∈ s, HahnSeries.single i (b i)) *
      (∑ j ∈ t, HahnSeries.single j (c j))) =
      derivative R (∑ i ∈ s, HahnSeries.single i (b i)) *
        (∑ j ∈ t, HahnSeries.single j (c j)) +
      (∑ i ∈ s, HahnSeries.single i (b i)) *
        derivative R (∑ j ∈ t, HahnSeries.single j (c j)) := by
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum,
    derivative_single_mul_single, Finset.sum_add_distrib]

/-- The Leibniz rule for the same canonical derivative, obtained by
passing the finite monomial identity through actual truncation limits. -/
theorem derivative_mul (f g : LaurentSeries R) :
    derivative R (f * g) = derivative R f * g + f * derivative R g := by
  let := orderTopology R
  have := orderTopology_isTopologicalRing (R := R)
  have := orderTopology_t2Space (R := R)
  have hf := tendsto_truncLT_orderTopology f
  have hg := tendsto_truncLT_orderTopology g
  apply tendsto_nhds_unique_of_forall
    ((continuous_derivative.tendsto (f * g)).comp (hf.mul hg))
    ((((continuous_derivative.tendsto f).comp hf).mul hg).add
      (hf.mul ((continuous_derivative.tendsto g).comp hg)))
  intro n
  simp only [Function.comp_def, truncLT_eq_sum_Ico]
  exact derivative_finite_sums_mul _ _ _ _

@[simp]
theorem derivative_one : derivative R (1 : LaurentSeries R) = 0 := by
  simpa only [HahnSeries.C_one] using derivative_C (R := R) 1

/-- The positive-power rule, stated without a truncated predecessor at zero. -/
theorem derivative_pow_succ (f : LaurentSeries R) (n : ℕ) :
    derivative R (f ^ (n + 1)) = ((n + 1 : ℕ) : LaurentSeries R) * f ^ n * derivative R f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ f (n + 1), derivative_mul, ih, pow_succ]
    push_cast
    ring

/-- The inverse-unit derivative formula requires no inverse operation on
the ambient coefficient or Laurent ring. -/
theorem derivative_units_inv (u : (LaurentSeries R)ˣ) :
    derivative R (↑(u⁻¹) : LaurentSeries R) =
      -((↑(u⁻¹) : LaurentSeries R) ^ 2 * derivative R (u : LaurentSeries R)) := by
  apply eq_neg_of_add_eq_zero_left
  calc
    _ = ((↑(u⁻¹) : LaurentSeries R) * ↑u) * derivative R (↑(u⁻¹) : LaurentSeries R) +
        (↑(u⁻¹) * ↑(u⁻¹)) * derivative R (u : LaurentSeries R) := by
      simp only [Units.inv_mul, one_mul, pow_two]
    _ = (↑(u⁻¹) : LaurentSeries R) * derivative R ((↑(u⁻¹) : LaurentSeries R) * ↑u) := by
      rw [derivative_mul]
      ring
    _ = 0 := by simp only [Units.inv_mul, derivative_one, mul_zero]

/-- The integer-power rule for an actual unit, including negative powers. -/
theorem derivative_units_zpow (u : (LaurentSeries R)ˣ) (j : ℤ) :
    derivative R (↑(u ^ j) : LaurentSeries R) =
      (j : LaurentSeries R) * (↑(u ^ (j - 1)) : LaurentSeries R) *
        derivative R (u : LaurentSeries R) := by
  cases j with
  | ofNat n =>
    cases n with
    | zero =>
      simpa only [Int.ofNat_eq_natCast, Nat.cast_zero, zpow_zero, Units.val_one,
        Int.cast_zero, zero_mul] using
        (derivative_one (R := R))
    | succ n =>
      simpa only [Int.ofNat_eq_natCast, Nat.succ_eq_add_one, Int.natCast_add, Int.natCast_one,
        add_sub_cancel_right, zpow_natCast, Units.val_pow_eq_pow_val,
        Int.cast_add, Int.cast_natCast, Int.cast_one, zpow_add, zpow_one, Units.val_mul,
        pow_succ, Nat.cast_add, Nat.cast_one] using derivative_pow_succ (u : LaurentSeries R) n
  | negSucc n =>
    have hj : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
    have he : -((n + 1 : ℕ) : ℤ) - 1 = -((n + 2 : ℕ) : ℤ) := by omega
    rw [hj, he]
    simp only [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [derivative_pow_succ, derivative_units_inv]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [pow_add]
    ring

section Evaluation

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

local notation "G" => U + HahnSeries.C δ * Y
local notation "laurentEval" => nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit

private theorem derivative_nilpotentLaurentEval_single (j : ℤ) (b : R) :
    derivative R (laurentEval (HahnSeries.single j b)) =
      laurentEval (derivative R (HahnSeries.single j b)) * derivative R G := by
  rw [nilpotentLaurentEval_single, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_units_zpow, derivative_single, nilpotentLaurentEval_single]
  simp only [map_mul, map_intCast, IsUnit.unit_spec]
  ring

private theorem derivative_nilpotentLaurentEval_truncLT (f : LaurentSeries R) (n : ℤ) :
    derivative R (laurentEval (HahnSeries.truncLT n f)) =
      laurentEval (derivative R (HahnSeries.truncLT n f)) * derivative R G := by
  simp only [truncLT_eq_sum_Ico, map_sum,
    derivative_nilpotentLaurentEval_single, Finset.sum_mul]

/-- The chain rule for actual Laurent evaluation. Both sides are the
limits of the corresponding finite-truncation identities in the named
Hausdorff order topology. -/
theorem derivative_nilpotentLaurentEval (f : LaurentSeries R) :
    derivative R (laurentEval f) = laurentEval (derivative R f) * derivative R G := by
  let := orderTopology R
  have := orderTopology_isTopologicalRing (R := R)
  have := orderTopology_t2Space (R := R)
  have ht := tendsto_truncLT_orderTopology f
  have hE := continuous_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
  apply tendsto_nhds_unique_of_forall
    ((continuous_derivative.tendsto (laurentEval f)).comp ((hE.tendsto f).comp ht))
    (((hE.tendsto (derivative R f)).comp
      ((continuous_derivative.tendsto f).comp ht)).mul tendsto_const_nhds)
  intro n
  exact derivative_nilpotentLaurentEval_truncLT δ U Y r hr hδ a c ha hc hU hY hUunit f n

end Evaluation

end

end LaurentSeries
