/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Evaluation
public import FalseTateNonliftability.LaurentSeries.OrderTopology

/-!
# The order estimate and continuity of Laurent evaluation

For nonnegative input order `N`, actual Laurent evaluation has output order
at least `a * N - (r - 1) * (a + c)`. This yields a uniform neighborhood
bound and continuity for the explicitly named Laurent order topology.
No estimate for negative input orders and no coefficient-domain hypothesis
are needed.

This is blueprint lemma `nl:laurent-evaluation-continuity`.
-/

@[expose] public section

namespace LaurentSeries

open Filter
open scoped Topology

noncomputable section

variable {R : Type*} [CommRing R]

/-- A Laurent series with no negative coefficients is the power series
formed from its unshifted nonnegative coefficients. -/
theorem ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero
    (f : LaurentSeries R) (hf : f ∈ orderAddSubgroup 0) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk (fun n : ℕ ↦ f.coeff n)) = f := by
  ext j
  rw [PowerSeries.coeff_coe]
  by_cases hj : j < 0
  · rw [ite_eq_left hj]
    exact ((mem_orderAddSubgroup_iff_coeff 0 f).mp hf j hj).symm
  · rw [ite_eq_right hj, PowerSeries.coeff_mk]
    exact congrArg f.coeff (Int.eq_natAbs_of_nonneg (le_of_not_gt hj)).symm

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop)

local notation "D" => ((r - 1 : ℕ) : ℤ) * (a + c)
local notation "powerEval" => nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY

/-- Vanishing of the first `N` power-series coefficients gives the precise
lower-order bound on the actual summable-power evaluation. -/
theorem nilpotentPowerSeriesEval_mem_orderAddSubgroup (N : ℕ) (f : PowerSeries R)
    (hf : ∀ n : ℕ, n < N → f.coeff n = 0) :
    powerEval f ∈ orderAddSubgroup (a * N - D) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [nilpotentPowerSeriesEval_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n < N
  · rw [hf n hn, zero_smul]
  · have hNn : (N : ℤ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hn
    have hbound : j < a * n - D :=
      hj.trans_le (sub_le_sub_right (mul_le_mul_of_nonneg_left hNn ha.le) D)
    have hpow := nilpotent_perturbation_orderTop_pow δ U Y r hr hδ a c ha hc hU hY n
    rw [HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hbound).trans_le hpow), smul_zero]

variable (hUunit : IsUnit U)

local notation "laurentEval" => nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit

/-- The actual Laurent evaluation maps a nonnegative order bound `N` to
the linearly growing bound `a * N - D`. Zero is included. -/
theorem nilpotentLaurentEval_mem_orderAddSubgroup (N : ℕ) (f : LaurentSeries R)
    (hf : f ∈ orderAddSubgroup (N : ℤ)) :
    laurentEval f ∈ orderAddSubgroup (a * N - D) := by
  have hf0 : f ∈ orderAddSubgroup 0 :=
    orderAddSubgroup_antitone (show (0 : ℤ) ≤ N by omega) hf
  rw [← ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero f hf0,
    nilpotentLaurentEval_ofPowerSeries]
  apply nilpotentPowerSeriesEval_mem_orderAddSubgroup δ U Y r hr hδ a c ha hc hU hY N
  intro n hn
  rw [PowerSeries.coeff_mk]
  exact (mem_orderAddSubgroup_iff_coeff (N : ℤ) f).mp hf n (by exact_mod_cast hn)

/-- A uniform nonnegative input-order threshold for every target neighborhood. -/
theorem nilpotentLaurentEval_exists_order_bound (M : ℤ) :
    ∃ N : ℕ, ∀ f : LaurentSeries R,
      f ∈ orderAddSubgroup (N : ℤ) → laurentEval f ∈ orderAddSubgroup M := by
  let N : ℕ := (M + D).toNat
  have hN : M + D ≤ (N : ℤ) := by omega
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg N
  have ha' : 1 ≤ a := ha
  have hbound : M ≤ a * N - D := by nlinarith
  refine ⟨N, fun f hf ↦ ?_⟩
  exact orderAddSubgroup_antitone hbound
    (nilpotentLaurentEval_mem_orderAddSubgroup δ U Y r hr hδ a c ha hc hU hY hUunit N f hf)

/-- The actual localization extension is continuous in the named order topology. -/
theorem continuous_nilpotentLaurentEval :
    @Continuous (LaurentSeries R) (LaurentSeries R) (orderTopology R) (orderTopology R)
      laurentEval := by
  let := orderTopology R
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto laurentEval (nhds x) (nhds (laurentEval x))
  rw [(orderTopology_hasBasis_nhds x).tendsto_iff
    (orderTopology_hasBasis_nhds (laurentEval x))]
  intro M _
  obtain ⟨N, hN⟩ :=
    nilpotentLaurentEval_exists_order_bound δ U Y r hr hδ a c ha hc hU hY hUunit M
  refine ⟨(N : ℤ), trivial, ?_⟩
  intro f hf
  simp only [Set.mem_ofPred_eq] at hf ⊢
  rw [← map_sub]
  exact hN (f - x) hf

end

end LaurentSeries
