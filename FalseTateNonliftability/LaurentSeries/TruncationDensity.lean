module

public import FalseTateNonliftability.LaurentSeries.EvaluationContinuity

/-!
# Finite Laurent truncations and continuous uniqueness

Actual strict truncations are finite integer-monomial sums and converge
in the named Laurent order topology. Their evaluated sums converge to
the actual Laurent evaluation. Continuous algebra homomorphisms into a
Hausdorff target are therefore determined by the image of the variable.

This is blueprint lemma `nl:laurent-truncation-density`.
-/

@[expose] public section

namespace LaurentSeries

open Filter
open scoped Topology

noncomputable section

variable {R : Type*} [CommRing R]

/-- The actual strict truncation is a finite monomial sum over the integer
interval from `order f` to the truncation bound. This includes `f = 0`. -/
theorem truncLT_eq_sum_Ico (f : LaurentSeries R) (n : ℤ) :
    HahnSeries.truncLT n f =
      ∑ j ∈ Finset.Ico f.order n, HahnSeries.single j (f.coeff j) := by
  classical
  ext j
  rw [HahnSeries.coeff_sum]
  by_cases hjn : j < n
  · rw [HahnSeries.coeff_truncLT_of_lt hjn]
    symm
    calc
      _ = (HahnSeries.single j (f.coeff j)).coeff j := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          exact HahnSeries.coeff_single_of_ne (Ne.symm hkj)
        · intro hjnot
          have hjlow : j < f.order := by
            by_contra! hge
            exact hjnot (Finset.mem_Ico.mpr ⟨hge, hjn⟩)
          rw [HahnSeries.coeff_single_same, HahnSeries.coeff_eq_zero_of_lt_order hjlow]
      _ = _ := HahnSeries.coeff_single_same j (f.coeff j)
  · rw [HahnSeries.coeff_truncLT_of_le (le_of_not_gt hjn)]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := (Finset.mem_Ico.mp hk).2
    exact HahnSeries.coeff_single_of_ne (by omega : j ≠ k)

/-- Natural strict truncations converge, retaining all negative terms
and agreeing eventually in every degree below each prescribed bound. -/
theorem tendsto_truncLT_orderTopology (f : LaurentSeries R) :
    Tendsto (fun n : ℕ ↦ HahnSeries.truncLT (n : ℤ) f) atTop
      (@nhds (LaurentSeries R) (orderTopology R) f) := by
  apply tendsto_orderTopology_iff.mpr
  intro m
  refine eventually_atTop.mpr ⟨m.toNat, ?_⟩
  intro n hn j hj
  apply HahnSeries.coeff_truncLT_of_lt
  omega

section Evaluation

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

local notation "laurentEval" => nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
local notation "gUnit" => IsUnit.unit
  (isUnit_nilpotent_perturbation δ U Y (Exists.intro r hδ) hUunit)

/-- Actual evaluation of each finite truncation is its finite sum of
constant coefficients times integer powers in the unit group. -/
theorem nilpotentLaurentEval_truncLT (f : LaurentSeries R) (n : ℤ) :
    laurentEval (HahnSeries.truncLT n f) =
      ∑ j ∈ Finset.Ico f.order n,
        HahnSeries.C (f.coeff j) * (↑(gUnit ^ j) : LaurentSeries R) := by
  rw [truncLT_eq_sum_Ico, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact nilpotentLaurentEval_single δ U Y r hr hδ a c ha hc hU hY hUunit j (f.coeff j)

/-- The actual evaluated finite sums, including the negative Laurent
prefix, converge to actual Laurent evaluation in the named order topology. -/
theorem tendsto_nilpotentLaurentEval_finite_sums (f : LaurentSeries R) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.Ico f.order (n : ℤ),
      HahnSeries.C (f.coeff j) * (↑(gUnit ^ j) : LaurentSeries R)) atTop
        (@nhds (LaurentSeries R) (orderTopology R) (laurentEval f)) := by
  let := orderTopology R
  have hcont := continuous_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
  have h := (hcont.tendsto f).comp (tendsto_truncLT_orderTopology f)
  simpa only [Function.comp_def, nilpotentLaurentEval_truncLT] using h

end Evaluation

section Uniqueness

variable {A : Type*} [CommRing A] [Algebra R A]

private theorem algHom_inv_variable_eq_of_X_eq
    (F H : LaurentSeries R →ₐ[R] A)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) =
      H (HahnSeries.single (1 : ℤ) (1 : R))) :
    F (HahnSeries.single (-1 : ℤ) (1 : R)) = H (HahnSeries.single (-1 : ℤ) (1 : R)) := by
  have hF : F (HahnSeries.single (1 : ℤ) (1 : R)) *
      F (HahnSeries.single (-1 : ℤ) (1 : R)) = 1 := by
    rw [← map_mul]
    simp
  have hH : F (HahnSeries.single (1 : ℤ) (1 : R)) *
      H (HahnSeries.single (-1 : ℤ) (1 : R)) = 1 := by
    rw [hX, ← map_mul]
    simp
  exact inv_unique hF hH

private theorem algHom_single_eq_of_X_eq
    (F H : LaurentSeries R →ₐ[R] A)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) =
      H (HahnSeries.single (1 : ℤ) (1 : R))) (j : ℤ) (b : R) :
    F (HahnSeries.single j b) = H (HahnSeries.single j b) := by
  have hneg := algHom_inv_variable_eq_of_X_eq F H hX
  have hone (n : ℤ) : F (HahnSeries.single n (1 : R)) = H (HahnSeries.single n (1 : R)) := by
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have hs : (HahnSeries.single ((n : ℤ) + 1) (1 : R) : LaurentSeries R) =
          HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 := by simp
      rw [hs, map_mul, map_mul, ih, hX]
    | pred n ih =>
      have hs : (HahnSeries.single (-(n : ℤ) - 1) (1 : R) : LaurentSeries R) =
          HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.single (-1 : ℤ) 1 := by
        simp [sub_eq_add_neg]
      rw [hs, map_mul, map_mul, ih, hneg]
  have hC : F (HahnSeries.C b) = H (HahnSeries.C b) := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using (F.commutes b).trans (H.commutes b).symm
  have hs : (HahnSeries.single j b : LaurentSeries R) =
      HahnSeries.C b * HahnSeries.single j 1 := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hs, map_mul, map_mul, hC, hone]

variable [TopologicalSpace A] [T2Space A]

/-- Continuous algebra homomorphisms from Laurent series with the named
order topology into a Hausdorff target are determined by the variable.
Only Hausdorffness of the target topology is needed for this uniqueness. -/
theorem continuous_algHom_ext_X (F H : LaurentSeries R →ₐ[R] A)
    (hF : @Continuous (LaurentSeries R) A (orderTopology R) inferInstance F)
    (hH : @Continuous (LaurentSeries R) A (orderTopology R) inferInstance H)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) =
      H (HahnSeries.single (1 : ℤ) (1 : R))) : F = H := by
  let := orderTopology R
  apply AlgHom.ext
  intro f
  apply tendsto_nhds_unique_of_forall
    ((hF.tendsto f).comp (tendsto_truncLT_orderTopology f))
    ((hH.tendsto f).comp (tendsto_truncLT_orderTopology f))
  intro n
  simp only [Function.comp_def, truncLT_eq_sum_Ico, map_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ algHom_single_eq_of_X_eq F H hX j (f.coeff j))

end Uniqueness

end

end LaurentSeries
