module

public import FalseTateNonliftability.LaurentSeries.NilpotentPower

/-!
# Power series evaluated at a nilpotent Laurent perturbation

Evaluation is the actual coefficientwise sum of the summable family
constructed in `NilpotentPower`. Multiplication is proved by finite
antidiagonal regrouping, so no positivity assumption on the order of
the perturbed series itself is required.

This is blueprint lemma `nl:power-series-evaluation`.
-/

@[expose] public section

namespace LaurentSeries

open HahnSeries Finset Function

noncomputable section

variable {R : Type*} [CommRing R]
variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop)

local notation "G" => U + HahnSeries.C δ * Y
local notation "family" => nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY

private theorem constant_smul_mul (b d : R) (x y : LaurentSeries R) :
    (b • x) * (d • y) = (b * d) • (x * y) := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul, map_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem productFamily_support_subset (f g : PowerSeries R) (j : ℤ) :
    ((family (fun n ↦ (f * g).coeff n)).coeff j).support ⊆
      (((family (fun n ↦ f.coeff n)).mul (family (fun n ↦ g.coeff n))).coeff j).support.image
        (fun ij ↦ ij.1 + ij.2) := by
  simp only [HahnSeries.SummableFamily.coeff_support, Set.Finite.toFinset_subset,
    support_subset_iff]
  intro n hn
  have he : ∃ ij ∈ antidiagonal n,
      f.coeff ij.1 • g.coeff ij.2 • (G ^ n).coeff j ≠ 0 := by
    refine exists_ne_zero_of_sum_ne_zero ?_
    simpa [PowerSeries.coeff_mul, sum_smul, mul_smul,
      nilpotentPowerFamily_apply, HahnSeries.coeff_smul] using hn
  obtain ⟨ij, hij, hne⟩ := he
  have hij' : ij.1 + ij.2 = n := HasAntidiagonal.mem_antidiagonal.mp hij
  simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
  refine ⟨ij, ?_, hij'⟩
  simp only [SummableFamily.mul_toFun, nilpotentPowerFamily_apply, Function.mem_support]
  rw [constant_smul_mul, ← pow_add, hij', HahnSeries.coeff_smul, mul_smul]
  exact hne

/-- Multiplication of the actual summable power families is compatible with
power-series convolution, by finite coefficientwise antidiagonal regrouping. -/
theorem hsum_nilpotentPowerFamily_mul (f g : PowerSeries R) :
    (family (fun n ↦ (f * g).coeff n)).hsum =
      ((family (fun n ↦ f.coeff n)).mul (family (fun n ↦ g.coeff n))).hsum := by
  ext j
  simp only [SummableFamily.coeff_hsum_eq_sum, SummableFamily.mul_toFun,
    nilpotentPowerFamily_apply, HahnSeries.coeff_smul,
    constant_smul_mul]
  rw [sum_subset (productFamily_support_subset δ U Y r hr hδ a c ha hc hU hY f g j)
    (fun i hi his ↦ by
      simpa [PowerSeries.coeff_mul, sum_smul, sum_mul] using his)]
  simp only [SummableFamily.coeff_support, SummableFamily.mul_toFun,
    nilpotentPowerFamily_apply, constant_smul_mul,
    HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
  rw [sum_sigma']
  refine (Finset.sum_of_injOn (fun ij : ℕ × ℕ ↦ ⟨ij.1 + ij.2, ij⟩)
    (fun _ _ _ _ ↦ by simp) ?_ ?_
    (fun _ _ ↦ by simp [mul_comm, pow_add])).symm
  · intro ij hij
    simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists,
      mem_coe, HasAntidiagonal.mem_antidiagonal, and_true]
    use ij.1, ij.2
    simp_all
  · intro i hi his
    have hz : ∀ m n : ℕ, (⟨m + n, (m, n)⟩ : Σ _ : ℕ, ℕ × ℕ) = i →
        g.coeff n • (f.coeff m • (G ^ m * G ^ n).coeff j) = 0 := by
      intro m n
      contrapose!
      simp only [Set.Finite.coe_toFinset, Set.mem_image, Function.mem_support,
        ne_eq, Prod.exists, not_exists, not_and] at his
      simpa only [constant_smul_mul, HahnSeries.coeff_smul, smul_eq_mul,
        mul_assoc, mul_comm, mul_left_comm] using his m n
    simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hi
    rw [mul_comm (f.coeff i.snd.1), ← hi.2, mul_smul, pow_add]
    exact hz i.snd.1 i.snd.2 (Sigma.eq hi.2 (by simp))

private theorem family_monomial (n : ℕ) (b : R) :
    family (fun k ↦ (PowerSeries.monomial n b).coeff k) =
      SummableFamily.single n (b • G ^ n) := by
  ext k
  by_cases hk : k = n <;>
    simp [nilpotentPowerFamily_apply, PowerSeries.coeff_monomial, hk]

/-- Evaluation of formal power series at the actual nilpotent perturbation,
defined by its summable family rather than a positive-order fallback. -/
def nilpotentPowerSeriesEval : PowerSeries R →ₐ[R] LaurentSeries R where
  toFun f := (family (fun n ↦ f.coeff n)).hsum
  map_one' := by
    change (family (fun n ↦ (PowerSeries.C (1 : R)).coeff n)).hsum = 1
    rw [show (PowerSeries.C (1 : R)) = PowerSeries.monomial 0 1 from
        congrFun PowerSeries.monomial_zero_eq_C.symm 1,
      family_monomial, SummableFamily.hsum_single]
    simp
  map_zero' := by
    have hzero : family (fun n ↦ (0 : PowerSeries R).coeff n) = 0 := by
      ext n
      simp [nilpotentPowerFamily_apply]
    rw [hzero, SummableFamily.hsum_zero]
  map_add' f g := by
    have hadd : family (fun n ↦ (f + g).coeff n) =
        family (fun n ↦ f.coeff n) + family (fun n ↦ g.coeff n) := by
      ext n
      simp [nilpotentPowerFamily_apply, add_smul]
    rw [hadd, SummableFamily.hsum_add]
  map_mul' f g := by
    rw [hsum_nilpotentPowerFamily_mul δ U Y r hr hδ a c ha hc hU hY,
      SummableFamily.hsum_mul]
  commutes' b := by
    simp only [PowerSeries.algebraMap_eq, HahnSeries.algebraMap_apply',
      HahnSeries.ofPowerSeries_C]
    change (family (fun n ↦ (PowerSeries.C b).coeff n)).hsum = HahnSeries.C b
    rw [show PowerSeries.C b = PowerSeries.monomial 0 b from
        congrFun PowerSeries.monomial_zero_eq_C.symm b,
      family_monomial, SummableFamily.hsum_single]
    rw [pow_zero, ← HahnSeries.C_mul_eq_smul, mul_one]

/-- Evaluation is exactly the sum of the constructed Laurent power family. -/
theorem nilpotentPowerSeriesEval_apply (f : PowerSeries R) :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY f =
      (family (fun n ↦ f.coeff n)).hsum := rfl

/-- Its coefficient is the finite-support sum of the actual weighted powers. -/
theorem nilpotentPowerSeriesEval_coeff (f : PowerSeries R) (j : ℤ) :
    (nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY f).coeff j =
      ∑ᶠ n : ℕ, f.coeff n • (G ^ n).coeff j := by
  simp only [nilpotentPowerSeriesEval_apply, SummableFamily.coeff_hsum,
    nilpotentPowerFamily_apply, HahnSeries.coeff_smul]

@[simp]
theorem nilpotentPowerSeriesEval_C (b : R) :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY (PowerSeries.C b) =
      HahnSeries.C b := by
  simpa only [PowerSeries.algebraMap_eq, HahnSeries.algebraMap_apply',
    HahnSeries.ofPowerSeries_C] using
    (nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY).commutes b

@[simp]
theorem nilpotentPowerSeriesEval_X :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY PowerSeries.X = G := by
  rw [PowerSeries.X_eq, nilpotentPowerSeriesEval_apply, family_monomial,
    SummableFamily.hsum_single]
  simp

end

end LaurentSeries
