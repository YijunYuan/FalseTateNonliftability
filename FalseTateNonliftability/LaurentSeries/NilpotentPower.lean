module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Powers of a nilpotently perturbed Laurent series

The powers of `U + C δ * Y` have linearly growing support bounds when
`U` has positive order and `δ` is nilpotent, even if `Y` has negative
order. Consequently arbitrary coefficient-weighted powers form an actual
`HahnSeries.SummableFamily`. No domain or reducedness hypothesis is used.

This is blueprint lemma `nl:nilpotent-power-order`.
-/

@[expose] public section

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

/-- A nilpotent perturbation of a positive-order series has powers with
linearly growing lower bounds, including when the perturbation has negative order. -/
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
      nlinarith
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

/-- A linearly growing integer lower bound gives an actual summable family
of Laurent series. The coefficients of each degree have finite co-support. -/
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
    have hnle : (n : ℤ) ≤ j + d := by nlinarith
    change n ≤ (j + d).toNat
    omega

@[simp]
theorem summableFamilyOfLinearOrderBound_apply
    (f : ℕ → LaurentSeries R) (a d : ℤ) (ha : 0 < a)
    (hf : ∀ n : ℕ, ((a * n - d : ℤ) : WithTop ℤ) ≤ (f n).orderTop) (n : ℕ) :
    summableFamilyOfLinearOrderBound f a d ha hf n = f n := rfl

/-- Arbitrary coefficient-weighted powers of a nilpotent perturbation form
a summable family, even when the perturbation itself has negative order. -/
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

@[simp]
theorem nilpotentPowerFamily_apply
    (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
    (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (b : ℕ → R) (n : ℕ) :
    nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY b n =
      b n • (U + HahnSeries.C δ * Y) ^ n := rfl

/-- The summable family's terms are exactly the expected constant multiples. -/
theorem nilpotentPowerFamily_apply_eq_C_mul
    (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
    (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
    (hU : (a : WithTop ℤ) ≤ U.orderTop)
    (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (b : ℕ → R) (n : ℕ) :
    nilpotentPowerFamily δ U Y r hr hδ a c ha hc hU hY b n =
      HahnSeries.C (b n) * (U + HahnSeries.C δ * Y) ^ n := by
  simp only [nilpotentPowerFamily_apply, HahnSeries.C_mul_eq_smul]

end

end LaurentSeries
