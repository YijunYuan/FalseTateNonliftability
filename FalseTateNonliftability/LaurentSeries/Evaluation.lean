/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Map
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Evaluation of Laurent series at a nilpotent perturbation of a unit

Let `R` be a commutative ring, let `δ ∈ R` with `δ ^ r = 0`, and let `G = U + δ Y` with
`U, Y ∈ R((T))`, where `U` is a unit with `U = O(T ^ a)` for some `a > 0` and `Y = O(T ^ (-c))`
with `c ≥ 0`. Then `G ^ n = O(T ^ (a n - (r - 1) (a + c)))`, so for every power series
`f = ∑ fₙ Xⁿ` over `R` the sum `f(G) = ∑ fₙ Gⁿ` converges coefficientwise, and `f ↦ f(G)` is an
`R`-algebra homomorphism `R⟦X⟧ → R((T))`. As `G` is a unit and `R((T))` is the localization of
`R⟦T⟧` at `T`, it extends to an `R`-algebra endomorphism `f ↦ f(G)` of `R((T))` sending `T` to
`G`. This endomorphism is continuous for the `T`-adic topology, satisfies the chain rule
`f(G)' = f'(G) G'` and commutes with coefficient maps.

If `δ` generates a maximal ideal of `R` and the reduction of `G ∈ R((T))` modulo `δ` has finite
order `a`, then `G = U + δ Y`, where `U = G - ∑_{j < a} G_j T ^ j` is a unit of order `a` and
`Y = O(T ^ (-c))` for some `c ≥ 0`. For `a > 0` this gives the substitution `f ↦ f(G)`
(`LaurentSeries.subst`), the map `Q ↦ Q ∘ G` of Yuan, Lemma 2.1.

## Main definitions

* `LaurentSeries.summableFamilyOfLinearOrderBound`: a family `(fₙ)` with
  `fₙ = O(T ^ (a n - d))`, `a > 0`, as a summable family.
* `LaurentSeries.nilpotentPowerFamily`: the summable family `(bₙ Gⁿ)ₙ`.
* `LaurentSeries.nilpotentPowerSeriesEval`: the evaluation `R⟦X⟧ →ₐ[R] R((T))`, `f ↦ f(G)`.
* `LaurentSeries.nilpotentLaurentEval`: its extension `R((T)) →ₐ[R] R((T))`.

## Main results

* `LaurentSeries.nilpotent_perturbation_orderTop_pow`: the lower bound on the order of `G ^ n`.
* `LaurentSeries.nilpotentLaurentEval_X`, `LaurentSeries.nilpotentLaurentEval_single`: the values
  on monomials.
* `LaurentSeries.continuous_nilpotentLaurentEval`: continuity for the `T`-adic topology.
* `LaurentSeries.derivative_nilpotentLaurentEval`: the chain rule.
* `LaurentSeries.mapRingHom_nilpotentLaurentEval`: compatibility with coefficient maps.
* `LaurentSeries.exists_nilpotentLaurentEval_data`: the decomposition `G = U + δ Y`.

## Implementation notes

The definitions take the decomposition `G = U + δ Y`, the integers `r`, `a`, `c` and the bounds
as arguments. They are the construction behind `LaurentSeries.subst`
(`FalseTateNonliftability.LaurentSeries.Substitution`), which depends on `G` alone and through
which the rest of the library uses them.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 2.1 (1), (2) (convergence of `Q ∘ G = ∑ aᵢ Gⁱ` and the chain rule).
-/

@[expose] public section

/-! ### Powers of a nilpotent perturbation of a unit -/

section NilpotentPower

namespace LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

private theorem orderTop_pow_ge (U : LaurentSeries R) (a : ℤ)
    (hU : (a : WithTop ℤ) ≤ U.orderTop) (n : ℕ) :
    ((a * n : ℤ) : WithTop ℤ) ≤ (U ^ n).orderTop := by
  calc
    _ = n • (a : WithTop ℤ) := by
      rw [← WithTop.coe_nsmul]
      congr 1
      simp [mul_comm]
    _ ≤ n • U.orderTop := nsmul_le_nsmul_right hU n
    _ ≤ _ := HahnSeries.orderTop_nsmul_le_orderTop_pow

/-- Let `δ ^ r = 0`, `U = O(T ^ a)` and `Y = O(T ^ (-c))` with `a > 0` and `c ≥ 0`. Then
`(U + δ Y) ^ n = O(T ^ (a n - (r - 1) (a + c)))`. -/
theorem nilpotent_perturbation_orderTop_pow
    (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
    (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (n : ℕ) :
    ((a * n - (r - 1 : ℕ) * (a + c) : ℤ) : WithTop ℤ) ≤
      ((U + HahnSeries.C δ * Y) ^ n).orderTop := by
  have hδY : ((-c : ℤ) : WithTop ℤ) ≤ (HahnSeries.C δ * Y).orderTop := by
    rw [HahnSeries.C_mul_eq_smul]
    exact hY.trans (HahnSeries.orderTop_le_orderTop_smul δ Y)
  rw [add_comm U, add_pow]
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro j hj
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkr : r ≤ k
  · have hzero : (HahnSeries.C δ * Y) ^ k = 0 := by
      rw [mul_pow, ← map_pow, pow_eq_zero_of_le hkr hδ, map_zero, zero_mul]
    simp only [hzero, zero_mul, HahnSeries.coeff_zero]
  · have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkr' : k ≤ r - 1 := by
      have : k < (r - 1) + 1 := by
        simpa only [Nat.sub_add_cancel hr] using Nat.lt_of_not_ge hkr
      omega
    have hlower : a * n - (r - 1 : ℕ) * (a + c) ≤
        (-c) * k + a * (n - k : ℕ) := by
      rw [Nat.cast_sub hkn]
      have hkR : (k : ℤ) ≤ (r - 1 : ℕ) := by exact_mod_cast hkr'
      have hac : 0 ≤ a + c := by omega
      linarith [mul_le_mul_of_nonneg_right hkR hac]
    have hprod : (((-c) * k + a * (n - k : ℕ) : ℤ) : WithTop ℤ) ≤
        ((HahnSeries.C δ * Y) ^ k * U ^ (n - k)).orderTop := by
      calc
        _ = (((-c) * k : ℤ) : WithTop ℤ) + ((a * (n - k : ℕ) : ℤ) : WithTop ℤ) :=
          WithTop.coe_add _ _
        _ ≤ ((HahnSeries.C δ * Y) ^ k).orderTop + (U ^ (n - k)).orderTop :=
          add_le_add (orderTop_pow_ge _ _ hδY k) (orderTop_pow_ge U a hU (n - k))
        _ ≤ _ := HahnSeries.orderTop_add_le_mul
    have hterm : (((-c) * k + a * (n - k : ℕ) : ℤ) : WithTop ℤ) ≤
        ((HahnSeries.C δ * Y) ^ k * U ^ (n - k) * (n.choose k : LaurentSeries R)).orderTop := by
      simpa only [nsmul_eq_mul, mul_comm] using hprod.trans
        (HahnSeries.orderTop_le_orderTop_smul (n.choose k)
          ((HahnSeries.C δ * Y) ^ k * U ^ (n - k)))
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (hj.trans_le ((WithTop.coe_le_coe.mpr hlower).trans hterm))

/-- A family `(fₙ)` of Laurent series with `fₙ = O(T ^ (a n - d))` for some `a > 0`, as a summable
family. -/
def summableFamilyOfLinearOrderBound (f : ℕ → LaurentSeries R) (a d : ℤ)
    (ha : 0 < a)
    (hf : ∀ n : ℕ, ((a * n - d : ℤ) : WithTop ℤ) ≤ (f n).orderTop) :
    HahnSeries.SummableFamily ℤ R ℕ where
  toFun := f
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-d, ?_⟩
    intro j hj
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hj
    have hdeg : a * n - d ≤ j := WithTop.coe_le_coe.mp
      ((hf n).trans (HahnSeries.orderTop_le_of_coeff_ne_zero hn))
    have han : 0 ≤ a * n := mul_nonneg ha.le (Nat.cast_nonneg n)
    omega
  finite_co_support' j := by
    apply (Set.finite_Iic (j + d).toNat).subset
    intro n hn
    have hdeg : a * n - d ≤ j := WithTop.coe_le_coe.mp
      ((hf n).trans (HahnSeries.orderTop_le_of_coeff_ne_zero hn))
    have ha' : 1 ≤ a := ha
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    have hnle : (n : ℤ) ≤ j + d := by linarith [mul_le_mul_of_nonneg_right ha' hn0]
    change n ≤ (j + d).toNat
    omega

/-- The summable family `(bₙ Gⁿ)ₙ`, where `G = U + δ Y` (see
`nilpotent_perturbation_orderTop_pow`). -/
def nilpotentPowerFamily
    (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
    (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (b : ℕ → R) :
    HahnSeries.SummableFamily ℤ R ℕ :=
  summableFamilyOfLinearOrderBound
    (fun n ↦ b n • (U + HahnSeries.C δ * Y) ^ n) a ((r - 1 : ℕ) * (a + c)) ha
    (fun n ↦ (nilpotent_perturbation_orderTop_pow δ U Y r hr hδ a c ha hc hU hY n).trans
      (HahnSeries.orderTop_le_orderTop_smul (b n) ((U + HahnSeries.C δ * Y) ^ n)))

/-- The `n`-th member of the family `(bₙ Gⁿ)ₙ` is `bₙ Gⁿ`. -/
@[simp]
theorem nilpotentPowerFamily_apply
    (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
    (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (b : ℕ → R) (n : ℕ) :
    nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY b n =
      b n • (U + HahnSeries.C δ * Y) ^ n := rfl

end

end LaurentSeries

end NilpotentPower

/-! ### Evaluation of power series -/

section PowerSeriesEval

namespace LaurentSeries

open HahnSeries Finset Function

noncomputable section

variable {R : Type*} [CommRing R]
variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop)

private theorem constant_smul_mul (b d : R) (x y : LaurentSeries R) :
    (b • x) * (d • y) = (b * d) • (x * y) := by
  rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul, map_mul]
  ring

private theorem productFamily_support_subset (f g : PowerSeries R) (j : ℤ) :
    ((nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ (f * g).coeff n)).coeff
        j).support ⊆
      (((nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ f.coeff n)).mul
        (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ g.coeff n))).coeff
          j).support.image (fun ij ↦ ij.1 + ij.2) := by
  intro n hn
  rw [Finsupp.mem_support_iff, SummableFamily.coeff_def] at hn
  obtain ⟨ij, hij, hne⟩ : ∃ ij ∈ antidiagonal n,
      f.coeff ij.1 • g.coeff ij.2 • ((U + HahnSeries.C δ * Y) ^ n).coeff j ≠ 0 := by
    refine exists_ne_zero_of_sum_ne_zero ?_
    simpa [PowerSeries.coeff_mul, sum_smul, mul_smul,
      nilpotentPowerFamily_apply, HahnSeries.coeff_smul] using hn
  have hij' : ij.1 + ij.2 = n := HasAntidiagonal.mem_antidiagonal.mp hij
  refine Finset.mem_image.mpr ⟨ij, ?_, hij'⟩
  rw [Finsupp.mem_support_iff, SummableFamily.coeff_def, SummableFamily.mul_toFun,
    nilpotentPowerFamily_apply, nilpotentPowerFamily_apply, constant_smul_mul, ← pow_add, hij',
    HahnSeries.coeff_smul, mul_smul]
  exact hne

/-- For power series `f` and `g`, the sum of the family `((f g)ₙ Gⁿ)ₙ` is the product of the sums
of the families `(fₙ Gⁿ)ₙ` and `(gₙ Gⁿ)ₙ`. -/
theorem hsum_nilpotentPowerFamily_mul (f g : PowerSeries R) :
    (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ (f * g).coeff n)).hsum =
      ((nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ f.coeff n)).mul
        (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ g.coeff n))).hsum := by
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
        g.coeff n • (f.coeff m •
          ((U + HahnSeries.C δ * Y) ^ m * (U + HahnSeries.C δ * Y) ^ n).coeff j) = 0 := by
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
    nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY
        (fun k ↦ (PowerSeries.monomial n b).coeff k) =
      SummableFamily.single n (b • (U + HahnSeries.C δ * Y) ^ n) := by
  ext k
  by_cases hk : k = n <;>
    simp [nilpotentPowerFamily_apply, PowerSeries.coeff_monomial, hk]

/-- The evaluation `f ↦ f(G) = ∑ fₙ Gⁿ` of power series at `G = U + δ Y`. -/
def nilpotentPowerSeriesEval : PowerSeries R →ₐ[R] LaurentSeries R where
  toFun f := (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ f.coeff n)).hsum
  map_one' := by
    change (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY
      (fun n ↦ (PowerSeries.C (1 : R)).coeff n)).hsum = 1
    rw [show (PowerSeries.C (1 : R)) = PowerSeries.monomial 0 1 from
        congrFun PowerSeries.monomial_zero_eq_C.symm 1,
      family_monomial, SummableFamily.hsum_single]
    simp
  map_zero' := by
    have hzero : nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY
        (fun n ↦ (0 : PowerSeries R).coeff n) = 0 := by
      ext n
      simp [nilpotentPowerFamily_apply]
    rw [hzero, SummableFamily.hsum_zero]
  map_add' f g := by
    have hadd : nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ (f + g).coeff n) =
        nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ f.coeff n) +
          nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ g.coeff n) := by
      ext n
      simp [nilpotentPowerFamily_apply, add_smul]
    rw [hadd, SummableFamily.hsum_add]
  map_mul' f g := by
    rw [hsum_nilpotentPowerFamily_mul δ U Y r hr hδ a c ha hc hU hY,
      SummableFamily.hsum_mul]
  commutes' b := by
    simp only [PowerSeries.algebraMap_eq, HahnSeries.algebraMap_apply',
      HahnSeries.ofPowerSeries_C]
    change (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY
      (fun n ↦ (PowerSeries.C b).coeff n)).hsum = HahnSeries.C b
    rw [show PowerSeries.C b = PowerSeries.monomial 0 b from
        congrFun PowerSeries.monomial_zero_eq_C.symm b,
      family_monomial, SummableFamily.hsum_single]
    rw [pow_zero, ← HahnSeries.C_mul_eq_smul, mul_one]

/-- `f(G)` is the sum of the family `(fₙ Gⁿ)ₙ`. -/
theorem nilpotentPowerSeriesEval_apply (f : PowerSeries R) :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY f =
      (nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY (fun n ↦ f.coeff n)).hsum := rfl

/-- The coefficient of `T ^ j` in `f(G)` is `∑ₙ fₙ (Gⁿ)_j`, a finite sum. -/
theorem nilpotentPowerSeriesEval_coeff (f : PowerSeries R) (j : ℤ) :
    (nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY f).coeff j =
      ∑ᶠ n : ℕ, f.coeff n • ((U + HahnSeries.C δ * Y) ^ n).coeff j := by
  simp only [nilpotentPowerSeriesEval_apply, SummableFamily.coeff_hsum,
    nilpotentPowerFamily_apply, HahnSeries.coeff_smul]

/-- A constant `b` evaluates to `b`. -/
@[simp]
theorem nilpotentPowerSeriesEval_C (b : R) :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY (PowerSeries.C b) =
      HahnSeries.C b := by
  simpa only [PowerSeries.algebraMap_eq, HahnSeries.algebraMap_apply',
    HahnSeries.ofPowerSeries_C] using
    (nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY).commutes b

/-- `X(G) = G`. -/
@[simp]
theorem nilpotentPowerSeriesEval_X :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY PowerSeries.X =
      U + HahnSeries.C δ * Y := by
  rw [PowerSeries.X_eq, nilpotentPowerSeriesEval_apply, family_monomial,
    SummableFamily.hsum_single]
  simp

end

end LaurentSeries

end PowerSeriesEval

/-! ### Evaluation of Laurent series -/

section LaurentEval

namespace LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- If `U` is a unit and `δ` is nilpotent, then `U + δ Y` is a unit. -/
theorem isUnit_nilpotent_perturbation (δ : R) (U Y : LaurentSeries R)
    (hδ : IsNilpotent δ) (hUunit : IsUnit U) : IsUnit (U + HahnSeries.C δ * Y) := by
  have hC : IsNilpotent (HahnSeries.C δ : LaurentSeries R) := hδ.map HahnSeries.C
  have hCY := (Commute.all (HahnSeries.C δ) Y).isNilpotent_mul_right hC
  exact hCY.isUnit_add_left_of_commute hUunit (Commute.all _ _)

-- The localization API uses the scalar actions of these algebras; their algebra maps agree
-- definitionally.
local instance : @IsScalarTower R (PowerSeries R) (LaurentSeries R)
    (inferInstance : Algebra R (PowerSeries R)).toSMul
    (inferInstance : Algebra (PowerSeries R) (LaurentSeries R)).toSMul
    (inferInstance : Algebra R (LaurentSeries R)).toSMul :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

/-- The evaluation `f ↦ f(G)` of Laurent series at `G = U + δ Y`: the extension of
`nilpotentPowerSeriesEval` along the localization `R⟦X⟧ → R((T))`, as `G` is a unit. -/
def nilpotentLaurentEval : LaurentSeries R →ₐ[R] LaurentSeries R :=
  IsLocalization.Away.liftAlgHom (S := LaurentSeries R)
    (f := nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY) PowerSeries.X <| by
    rw [nilpotentPowerSeriesEval_X]
    exact isUnit_nilpotent_perturbation δ U Y ⟨r, hδ⟩ hUunit

/-- On power series, `nilpotentLaurentEval` is `nilpotentPowerSeriesEval`. -/
@[simp]
theorem nilpotentLaurentEval_ofPowerSeries (f : PowerSeries R) :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
        (HahnSeries.ofPowerSeries ℤ R f) =
      nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY f := by
  simp only [nilpotentLaurentEval, IsLocalization.Away.liftAlgHom_apply]
  exact IsLocalization.Away.lift_eq _ _ f

/-- A constant `b` evaluates to `b`. -/
@[simp]
theorem nilpotentLaurentEval_C (b : R) :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit (HahnSeries.C b) =
      HahnSeries.C b := by
  simpa only [HahnSeries.ofPowerSeries_C, nilpotentPowerSeriesEval_C] using
    nilpotentLaurentEval_ofPowerSeries δ U Y r hr hδ a c ha hc hU hY hUunit (PowerSeries.C b)

/-- `T(G) = G`. -/
@[simp]
theorem nilpotentLaurentEval_X :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
        (HahnSeries.single (1 : ℤ) (1 : R)) =
      U + HahnSeries.C δ * Y := by
  simpa only [HahnSeries.ofPowerSeries_X, nilpotentPowerSeriesEval_X] using
    nilpotentLaurentEval_ofPowerSeries δ U Y r hr hδ a c ha hc hU hY hUunit PowerSeries.X

/-- `T⁻¹(G) = G⁻¹`. -/
@[simp]
theorem nilpotentLaurentEval_X_inv :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
        (HahnSeries.single (-1 : ℤ) (1 : R)) =
      (↑(isUnit_nilpotent_perturbation δ U Y ⟨r, hδ⟩ hUunit).unit⁻¹ : LaurentSeries R) := by
  apply Units.eq_inv_of_mul_eq_one_left
  rw [IsUnit.unit_spec, ← nilpotentLaurentEval_X δ U Y r hr hδ a c ha hc hU hY hUunit,
    ← map_mul]
  simp

/-- `(T ^ n)(G) = G ^ n` for `n ∈ ℤ`. -/
theorem nilpotentLaurentEval_single_one (n : ℤ) :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit (HahnSeries.single n (1 : R)) =
      (↑((isUnit_nilpotent_perturbation δ U Y ⟨r, hδ⟩ hUunit).unit ^ n) : LaurentSeries R) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hs : (HahnSeries.single ((n : ℤ) + 1) (1 : R) : LaurentSeries R) =
        HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 := by simp
    rw [hs, map_mul, ih, nilpotentLaurentEval_X, zpow_add, zpow_one,
      Units.val_mul, IsUnit.unit_spec]
  | pred n ih =>
    have hs : (HahnSeries.single (-(n : ℤ) - 1) (1 : R) : LaurentSeries R) =
        HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.single (-1 : ℤ) 1 := by
      simp [sub_eq_add_neg]
    rw [hs, map_mul, ih, nilpotentLaurentEval_X_inv, zpow_sub, zpow_one, Units.val_mul]

/-- `(b T ^ n)(G) = b G ^ n` for `n ∈ ℤ`. -/
theorem nilpotentLaurentEval_single (n : ℤ) (b : R) :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit (HahnSeries.single n b) =
      HahnSeries.C b *
        (↑((isUnit_nilpotent_perturbation δ U Y ⟨r, hδ⟩ hUunit).unit ^ n) : LaurentSeries R) := by
  have hs : (HahnSeries.single n b : LaurentSeries R) =
      HahnSeries.C b * HahnSeries.single n 1 := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hs, map_mul, nilpotentLaurentEval_C, nilpotentLaurentEval_single_one]

end

end LaurentSeries

end LaurentEval

/-! ### Continuity of evaluation -/

section EvaluationContinuity

namespace LaurentSeries

open Filter
open scoped Topology LaurentSeries.OrderTopology

noncomputable section

variable {R : Type*} [CommRing R]

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop)

/-- If `f = O(X ^ N)`, then `f(G) = O(T ^ (a N - (r - 1) (a + c)))`. -/
theorem nilpotentPowerSeriesEval_mem_orderAddSubgroup (N : ℕ) (f : PowerSeries R)
    (hf : ∀ n : ℕ, n < N → f.coeff n = 0) :
    nilpotentPowerSeriesEval δ U Y r hr hδ a c ha hc hU hY f ∈
      orderAddSubgroup (a * N - ((r - 1 : ℕ) : ℤ) * (a + c)) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [nilpotentPowerSeriesEval_coeff]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n < N
  · rw [hf n hn, zero_smul]
  · have hNn : (N : ℤ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hn
    have hbound : j < a * n - ((r - 1 : ℕ) : ℤ) * (a + c) :=
      hj.trans_le (sub_le_sub_right (mul_le_mul_of_nonneg_left hNn ha.le) _)
    have hpow := nilpotent_perturbation_orderTop_pow δ U Y r hr hδ a c ha hc hU hY n
    rw [HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hbound).trans_le hpow), smul_zero]

variable (hUunit : IsUnit U)

/-- If `f = O(T ^ N)` with `N ≥ 0`, then `f(G) = O(T ^ (a N - (r - 1) (a + c)))`. -/
theorem nilpotentLaurentEval_mem_orderAddSubgroup (N : ℕ) (f : LaurentSeries R)
    (hf : f ∈ orderAddSubgroup (N : ℤ)) :
    nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit f ∈
      orderAddSubgroup (a * N - ((r - 1 : ℕ) : ℤ) * (a + c)) := by
  have hf0 : f ∈ orderAddSubgroup 0 :=
    orderAddSubgroup_antitone (show (0 : ℤ) ≤ N by omega) hf
  rw [← ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero f hf0,
    nilpotentLaurentEval_ofPowerSeries]
  apply nilpotentPowerSeriesEval_mem_orderAddSubgroup δ U Y r hr hδ a c ha hc hU hY N
  intro n hn
  rw [PowerSeries.coeff_mk]
  exact (mem_orderAddSubgroup_iff_coeff (N : ℤ) f).mp hf n (by exact_mod_cast hn)

/-- For every `M` there is `N ≥ 0` such that `f = O(T ^ N)` implies `f(G) = O(T ^ M)`. -/
theorem nilpotentLaurentEval_exists_order_bound (M : ℤ) :
    ∃ N : ℕ, ∀ f : LaurentSeries R, f ∈ orderAddSubgroup (N : ℤ) →
      nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit f ∈ orderAddSubgroup M := by
  let N : ℕ := (M + ((r - 1 : ℕ) : ℤ) * (a + c)).toNat
  have hN : M + ((r - 1 : ℕ) : ℤ) * (a + c) ≤ (N : ℤ) := by omega
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg N
  have ha' : 1 ≤ a := ha
  have hbound : M ≤ a * N - ((r - 1 : ℕ) : ℤ) * (a + c) := by
    linarith [mul_le_mul_of_nonneg_right ha' hN0]
  refine ⟨N, fun f hf ↦ ?_⟩
  exact orderAddSubgroup_antitone hbound
    (nilpotentLaurentEval_mem_orderAddSubgroup δ U Y r hr hδ a c ha hc hU hY hUunit N f hf)

/-- The evaluation `f ↦ f(G)` is continuous for the `T`-adic topology. -/
theorem continuous_nilpotentLaurentEval :
    Continuous (nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  refine ((orderTopology_hasBasis_nhds x).tendsto_iff
    (orderTopology_hasBasis_nhds _)).mpr fun M _ ↦ ?_
  obtain ⟨N, hN⟩ :=
    nilpotentLaurentEval_exists_order_bound δ U Y r hr hδ a c ha hc hU hY hUunit M
  refine ⟨(N : ℤ), trivial, ?_⟩
  intro f hf
  simp only [Set.mem_ofPred_eq] at hf ⊢
  rw [← map_sub]
  exact hN (f - x) hf

end

end LaurentSeries

end EvaluationContinuity

/-! ### The chain rule -/

section ChainRule

namespace LaurentSeries

open Filter
open scoped Topology LaurentSeries.OrderTopology

noncomputable section

variable {R : Type*} [CommRing R]

section Evaluation

variable (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

private theorem derivative_nilpotentLaurentEval_single (j : ℤ) (b : R) :
    derivative R
        (nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit (HahnSeries.single j b)) =
      nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
          (derivative R (HahnSeries.single j b)) *
        derivative R (U + HahnSeries.C δ * Y) := by
  rw [nilpotentLaurentEval_single, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_units_zpow, derivative_single, nilpotentLaurentEval_single]
  simp only [map_mul, map_intCast, IsUnit.unit_spec]
  ring

private theorem derivative_nilpotentLaurentEval_truncLT (f : LaurentSeries R) (n : ℤ) :
    derivative R
        (nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit (HahnSeries.truncLT n f)) =
      nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
          (derivative R (HahnSeries.truncLT n f)) *
        derivative R (U + HahnSeries.C δ * Y) := by
  simp only [truncLT_eq_sum_Ico, map_sum,
    derivative_nilpotentLaurentEval_single, Finset.sum_mul]

/-- The chain rule `f(G)' = f'(G) G'`. -/
theorem derivative_nilpotentLaurentEval (f : LaurentSeries R) :
    derivative R (nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit f) =
      nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit (derivative R f) *
        derivative R (U + HahnSeries.C δ * Y) := by
  have ht := tendsto_truncLT_orderTopology f
  have hE := continuous_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
  apply tendsto_nhds_unique_of_forall
    ((continuous_derivative.tendsto _).comp ((hE.tendsto f).comp ht))
    (((hE.tendsto (derivative R f)).comp
      ((continuous_derivative.tendsto f).comp ht)).mul tendsto_const_nhds)
  intro n
  exact derivative_nilpotentLaurentEval_truncLT δ U Y r hr hδ a c ha hc hU hY hUunit f n

end Evaluation

end

end LaurentSeries

end ChainRule

/-! ### Coefficient maps -/

section CoefficientMap

namespace LaurentSeries

open Filter
open scoped Topology LaurentSeries.OrderTopology

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

section Evaluation

variable (ψ : R →+* S)
  (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

private theorem mapRingHom_algHom_apply {E : LaurentSeries R →ₐ[R] LaurentSeries R}
    {E' : LaurentSeries S →ₐ[S] LaurentSeries S} (hE : Continuous E) (hE' : Continuous E')
    (hX : mapRingHom ψ (E (HahnSeries.single (1 : ℤ) (1 : R))) =
      E' (HahnSeries.single (1 : ℤ) (1 : S))) (f : LaurentSeries R) :
    mapRingHom ψ (E f) = E' (mapRingHom ψ f) := by
  have hER (b : R) : E (HahnSeries.C b) = HahnSeries.C b := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using E.commutes b
  have hES (b : S) : E' (HahnSeries.C b) = HahnSeries.C b := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using E'.commutes b
  have heq : (mapRingHom ψ).comp E.toRingHom = E'.toRingHom.comp (mapRingHom ψ) := by
    apply continuous_ringHom_ext ((mapRingHom ψ).comp E.toRingHom)
      (E'.toRingHom.comp (mapRingHom ψ)) ((continuous_mapRingHom ψ).comp hE)
      (hE'.comp (continuous_mapRingHom ψ))
    · intro b
      change mapRingHom ψ (E (HahnSeries.C b)) = E' (mapRingHom ψ (HahnSeries.C b))
      rw [hER, mapRingHom_C, hES]
    · change mapRingHom ψ (E (HahnSeries.single (1 : ℤ) (1 : R))) =
        E' (mapRingHom ψ (HahnSeries.single (1 : ℤ) (1 : R)))
      rw [mapRingHom_single, map_one ψ, hX]
  exact RingHom.congr_fun heq f

/-- Evaluation commutes with coefficient maps: `ψ(f(G)) = ψ(f)(ψ(G))`. -/
theorem mapRingHom_nilpotentLaurentEval (f : LaurentSeries R) :
    mapRingHom ψ (nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit f) =
      nilpotentLaurentEval (ψ δ) (mapRingHom ψ U) (mapRingHom ψ Y) r hr
        (Eq.trans (Eq.symm (map_pow ψ δ r)) (Eq.trans (congrArg ψ hδ) (map_zero ψ))) a c ha hc
        (le_trans hU (orderTop_le_mapRingHom ψ U)) (le_trans hY (orderTop_le_mapRingHom ψ Y))
        (IsUnit.map (mapRingHom ψ) hUunit) (mapRingHom ψ f) :=
  mapRingHom_algHom_apply ψ (continuous_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit)
    (continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _)
    (by simp only [nilpotentLaurentEval_X, map_add, map_mul, mapRingHom_C]) f

end Evaluation

end

end LaurentSeries

end CoefficientMap

/-! ### Decomposition of a series of finite reduced order -/

section Admissible

namespace LaurentSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- If the reduction of `G` modulo `δ` is `O(T ^ a)`, then so is the reduction of
`∑_{j < a} G_j T ^ j`, which is therefore zero. -/
theorem principalReduction_truncLT_eq_zero (δ : R) (G : LaurentSeries R) (a : ℤ)
    (horder : (a : WithTop ℤ) ≤ (principalReduction δ G).orderTop) :
    principalReduction δ (HahnSeries.truncLT a G) = 0 := by
  ext j
  simp only [principalReduction_coeff, HahnSeries.coeff_zero]
  by_cases hj : j < a
  · rw [HahnSeries.coeff_truncLT_of_lt hj]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hj).trans_le horder)
  · rw [HahnSeries.coeff_truncLT_of_le (le_of_not_gt hj), map_zero]

private theorem orderTop_sub_truncLT_of_reduction_order
    (δ : R) (G : LaurentSeries R) (a : ℤ)
    (horder : (principalReduction δ G).orderTop = (a : WithTop ℤ)) :
    (G - HahnSeries.truncLT a G).orderTop = (a : WithTop ℤ) := by
  have hG : G.coeff a ≠ 0 := by
    intro hzero
    have hred := HahnSeries.coeff_orderTop_ne horder
    apply hred
    simp only [principalReduction_coeff, hzero, map_zero]
  have htail : (G - HahnSeries.truncLT a G).coeff a ≠ 0 := by
    simpa only [HahnSeries.coeff_sub, HahnSeries.coeff_truncLT_of_le le_rfl, sub_zero] using hG
  exact le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero htail)
    (sub_truncLT_mem_orderAddSubgroup G a)

/-- Let `δ` be nilpotent. If the reduction of `G` modulo `δ` has order `a` and a unit leading
coefficient, then `G - ∑_{j < a} G_j T ^ j` is a unit. -/
theorem isUnit_sub_truncLT_of_isUnit_reduction_coeff
    (δ : R) (G : LaurentSeries R) (hδ : IsNilpotent δ) (a : ℤ)
    (horder : (principalReduction δ G).orderTop = (a : WithTop ℤ))
    (hunit : IsUnit ((principalReduction δ G).coeff a)) :
    IsUnit (G - HahnSeries.truncLT a G) := by
  have hI : IsNilpotent (Ideal.span ({δ} : Set R)) := by
    obtain ⟨r, hr⟩ := hδ
    refine ⟨r, ?_⟩
    change Ideal.span ({δ} : Set R) ^ r = ⊥
    rw [Ideal.span_singleton_pow, hr, Ideal.span_singleton_zero]
  have hcoeff : IsUnit (G.coeff a) := hI.isUnit_quotient_mk_iff.mp hunit
  have htailorder := orderTop_sub_truncLT_of_reduction_order δ G a horder
  have htailne : G - HahnSeries.truncLT a G ≠ 0 := by
    apply HahnSeries.orderTop_ne_top.mp
    rw [htailorder]
    exact WithTop.coe_ne_top
  have htailorder' : (G - HahnSeries.truncLT a G).order = a := by
    exact WithTop.coe_inj.mp
      ((HahnSeries.order_eq_orderTop_of_ne_zero htailne).trans htailorder)
  have hlead : IsUnit (G - HahnSeries.truncLT a G).leadingCoeff := by
    simpa only [HahnSeries.leadingCoeff_eq, htailorder', HahnSeries.coeff_sub,
      HahnSeries.coeff_truncLT_of_le le_rfl, sub_zero] using hcoeff
  exact HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder hlead (AddGroup.isAddUnit _)

/-- Let `δ ^ r = 0` with `(δ)` maximal. If the reduction of `G` modulo `δ` has order `a`, then
`G = U + δ Y`, where `U = G - ∑_{j < a} G_j T ^ j` is a unit of order `a` and `Y = O(T ^ (-c))`
for some `c ≥ 0`. -/
theorem exists_nilpotentLaurentEval_data
    (δ : R) (G : LaurentSeries R) (r : ℕ) (hδ : δ ^ r = 0)
    [(Ideal.span ({δ} : Set R)).IsMaximal] (a : ℤ)
    (horder : (principalReduction δ G).orderTop = (a : WithTop ℤ)) :
    ∃ U Y : LaurentSeries R, ∃ c : ℤ,
      U = G - HahnSeries.truncLT a G ∧
      G = U + HahnSeries.C δ * Y ∧
      U.orderTop = (a : WithTop ℤ) ∧ IsUnit U ∧
      0 ≤ c ∧ ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop := by
  let := Ideal.Quotient.field (Ideal.span ({δ} : Set R))
  have hprefix : HahnSeries.truncLT a G ∈ Ideal.span {HahnSeries.C δ} := by
    rw [← ker_principalReduction, RingHom.mem_ker]
    exact principalReduction_truncLT_eq_zero δ G a horder.ge
  obtain ⟨Y, hY⟩ := Ideal.mem_span_singleton.mp hprefix
  have htailunit : IsUnit (G - HahnSeries.truncLT a G) :=
    isUnit_sub_truncLT_of_isUnit_reduction_coeff δ G ⟨r, hδ⟩ a horder
      (isUnit_iff_ne_zero.mpr (HahnSeries.coeff_orderTop_ne horder))
  refine ⟨G - HahnSeries.truncLT a G, Y, max (-Y.order) 0, rfl, ?_,
    orderTop_sub_truncLT_of_reduction_order δ G a horder, htailunit, le_max_right _ _, ?_⟩
  · rw [← hY]
    exact (sub_add_cancel G (HahnSeries.truncLT a G)).symm
  · exact (WithTop.coe_le_coe.mpr (show -max (-Y.order) 0 ≤ Y.order by omega)).trans
      (mem_orderAddSubgroup_order Y)

end

end LaurentSeries

end Admissible
