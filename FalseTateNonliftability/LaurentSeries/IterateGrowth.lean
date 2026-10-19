module

public import FalseTateNonliftability.LaurentSeries.NormalForm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Ramification growth of actual infinite-order substitutions

The actual difference operator gives the sharp bound `i(g^p) ≥ p * i(g)`,
including an identity output of infinite order. For an actual infinite-order
substitution tangent to the identity, every prime-power iterate has finite
positive ramification number; these numbers strictly increase and diverge.

This proves `nl:iterate-ramification-growth`, over any field of characteristic
`p`. The prime `2` is included.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

open Filter

variable {k : Type*} [Field k]

local instance iterateGrowthZeroSpanIsMaximal : (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- The sharp prime-fold bound follows from the actual characteristic-prime
difference identity and its valuation-raising property. Zero output is allowed. -/
theorem prime_iterate_sub_variable_mem (p : ℕ) [Fact p.Prime] [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) (d : ℤ) (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) :
    (subst 0 IsNilpotent.zero g hG)^[p] (HahnSeries.single (1 : ℤ) 1) -
        HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup ((p : ℤ) * d + 1) := by
  rw [← substitutionDifference_pow_char p g hG]
  simpa only [add_comm] using substitutionDifference_pow_mem g hG d hd hg p 1
    (HahnSeries.single (1 : ℤ) 1) (show HahnSeries.single (1 : ℤ) (1 : k) ∈ orderAddSubgroup 1
      from HahnSeries.orderTop_single_le)

/-- The actual automorphism at the original power-series iterate is the
power of the original automorphism, on the entire Laurent carrier. -/
theorem powerSeriesSubstEquiv_powerSeriesIterate (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1)) (n : ℕ) :
    powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesIterate f n)
        (powerSeriesIterate_spec f hf n).1
        (by rw [(powerSeriesIterate_spec f hf n).2]; exact hflinear.pow n) =
      (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear) ^ n := by
  let := orderTopology k
  have := orderTopology_t2Space (R := k)
  have heq : (powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesIterate f n)
        (powerSeriesIterate_spec f hf n).1
        (by rw [(powerSeriesIterate_spec f hf n).2]; exact hflinear.pow n)).toAlgHom =
      ((powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear) ^ n).toAlgHom := by
    apply continuous_algHom_ext_X
    · exact continuous_powerSeriesSubstEquiv _ _ _ _ _
    · simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_pow] using
        (continuous_powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear).iterate n
    · simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_pow, HahnSeries.ofPowerSeries_X] using
        powerSeriesSubstEquiv_iterate_ofPowerSeries f hf hflinear n PowerSeries.X
  exact AlgEquiv.ext fun x ↦ AlgHom.congr_fun heq x

/-- An actual infinite-order substitution has no identity positive iterate
in the original power-series carrier. Continuity extends equality from `X`. -/
theorem powerSeriesIterate_ne_X_of_infiniteOrder (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear))
    (n : ℕ) (hn : 0 < n) : powerSeriesIterate f n ≠ PowerSeries.X := by
  intro hidentity
  let := orderTopology k
  have := orderTopology_t2Space (R := k)
  let E := powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear
  have hX : (E ^ n) (HahnSeries.single (1 : ℤ) 1) = HahnSeries.single (1 : ℤ) 1 := by
    simpa only [E, AlgEquiv.coe_pow, hidentity, HahnSeries.ofPowerSeries_X] using
      (ofPowerSeries_powerSeriesIterate f hf hflinear n).symm
  have hmaps : (E ^ n).toAlgHom = (1 : LaurentSeries k ≃ₐ[k] LaurentSeries k).toAlgHom := by
    apply continuous_algHom_ext_X
    · simpa only [E, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_pow] using
        (continuous_powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear).iterate n
    · exact continuous_id
    · exact hX
  apply hinfinite
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, AlgEquiv.ext fun x ↦ AlgHom.congr_fun hmaps x⟩

/-- Every positive iterate of an actual infinite-order substitution has
nonzero Laurent displacement, so its order is finite. -/
theorem powerSeriesIterate_displacement_ne_zero (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf hflinear))
    (n : ℕ) (hn : 0 < n) :
    HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f n) - HahnSeries.single (1 : ℤ) 1 ≠ 0 := by
  intro hzero
  apply powerSeriesIterate_ne_X_of_infiniteOrder f hf hflinear hinfinite n hn
  have heq : HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f n) =
      HahnSeries.ofPowerSeries ℤ k PowerSeries.X := by
    simpa only [HahnSeries.ofPowerSeries_X, sub_eq_zero] using hzero
  ext j
  simpa only [HahnSeries.ofPowerSeries_apply_coeff] using
    congrArg (fun x : LaurentSeries k ↦ x.coeff (j : ℤ)) heq

/-- Tangency to the identity is preserved in every original power-series
iterate, expressed as the actual order-two support condition. -/
theorem powerSeriesIterate_sub_variable_mem_two (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) (n : ℕ) :
    HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f n) - HahnSeries.single (1 : ℤ) 1 ∈
      orderAddSubgroup 2 := by
  have hspec := powerSeriesIterate_spec f hf n
  simpa only [hspec.2, hlinear, one_pow] using
    ofPowerSeries_sub_linear_mem_two (powerSeriesIterate f n) hspec.1

/-- For a tangent substitution of infinite order, every positive iterate
has finite displacement order at least two. -/
theorem two_le_order_powerSeriesIterate_displacement (f : PowerSeries k)
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one))) (n : ℕ) (hn : 0 < n) :
    2 ≤ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f n) -
      HahnSeries.single (1 : ℤ) 1).order := by
  have hmem := powerSeriesIterate_sub_variable_mem_two f hf hlinear n
  change ((2 : ℤ) : WithTop ℤ) ≤ _ at hmem
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero
    (powerSeriesIterate_displacement_ne_zero f hf _ hinfinite n hn)] at hmem
  exact WithTop.coe_le_coe.mp hmem

/-- The sharp prime-fold estimate on successive actual prime-power
power-series iterates. Identity outputs retain their infinite order. -/
theorem primePowerIterate_sub_variable_mem (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hflinear : IsUnit (f.coeff 1))
    (n : ℕ) (d : ℤ) (hd : 1 ≤ d)
    (hg : HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
      HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) :
    HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ (n + 1))) -
      HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup ((p : ℤ) * d + 1) := by
  have hlinear : IsUnit ((powerSeriesIterate f (p ^ n)).coeff 1) := by
    rw [(powerSeriesIterate_spec f hf (p ^ n)).2]
    exact hflinear.pow _
  have hbound := prime_iterate_sub_variable_mem p
    (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)))
    (isAdmissible_ofPowerSeries 0 _ (powerSeriesIterate_spec f hf (p ^ n)).1 hlinear) d hd hg
  change (powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesIterate f (p ^ n))
      (powerSeriesIterate_spec f hf (p ^ n)).1 hlinear)^[p]
        (HahnSeries.single (1 : ℤ) 1) - HahnSeries.single (1 : ℤ) 1 ∈ _ at hbound
  have heq : (powerSeriesSubstEquiv 0 IsNilpotent.zero (powerSeriesIterate f (p ^ n))
      (powerSeriesIterate_spec f hf (p ^ n)).1 hlinear)^[p]
        (HahnSeries.single (1 : ℤ) 1) =
      HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ (n + 1))) := by
    rw [← AlgEquiv.coe_pow, powerSeriesSubstEquiv_powerSeriesIterate f hf hflinear,
      ← pow_mul, ← pow_succ p n, AlgEquiv.coe_pow]
    exact (ofPowerSeries_powerSeriesIterate f hf hflinear (p ^ (n + 1))).symm
  rwa [heq] at hbound

/-- Successive finite ramification numbers satisfy the sharp multiplicative
growth bound. Finiteness follows from the actual infinite-order automorphism. -/
theorem primePowerIterate_ramification_growth (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one))) (n : ℕ) :
    (p : ℤ) * ((HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
        HahnSeries.single (1 : ℤ) 1).order - 1) ≤
      (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ (n + 1))) -
        HahnSeries.single (1 : ℤ) 1).order - 1 := by
  let D := fun n : ℕ ↦ HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
    HahnSeries.single (1 : ℤ) 1
  have hn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hnext : 0 < p ^ (n + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hd : 1 ≤ (D n).order - 1 := by
    have := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite (p ^ n) hn
    dsimp only [D]
    omega
  have hmem : D n ∈ orderAddSubgroup ((D n).order - 1 + 1) := by
    simpa only [sub_add_cancel] using mem_orderAddSubgroup_order (D n)
  have hbound := primePowerIterate_sub_variable_mem p f hf
    (by rw [hlinear]; exact isUnit_one) n ((D n).order - 1) hd hmem
  change (((p : ℤ) * ((D n).order - 1) + 1 : ℤ) : WithTop ℤ) ≤ (D (n + 1)).orderTop at hbound
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero
    (powerSeriesIterate_displacement_ne_zero f hf _ hinfinite (p ^ (n + 1)) hnext)] at hbound
  have h : (p : ℤ) * ((D n).order - 1) + 1 ≤ (D (n + 1)).order :=
    WithTop.coe_le_coe.mp hbound
  change (p : ℤ) * ((D n).order - 1) ≤ (D (n + 1)).order - 1
  omega

/-- The actual finite prime-power ramification numbers strictly increase,
including in characteristic two. -/
theorem strictMono_primePowerIterate_ramification (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one))) :
    StrictMono (fun n : ℕ ↦ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
      HahnSeries.single (1 : ℤ) 1).order - 1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hbound := primePowerIterate_ramification_growth p f hf hlinear hinfinite n
  have horder := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos _)
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  nlinarith

/-- The actual finite ramification numbers of an infinite-order tangent
substitution diverge in the ordinary integer order. -/
theorem tendsto_primePowerIterate_ramification_atTop (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : PowerSeries k) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one))) :
    Tendsto (fun n : ℕ ↦ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
      HahnSeries.single (1 : ℤ) 1).order - 1) atTop atTop := by
  let d := fun n : ℕ ↦ (HahnSeries.ofPowerSeries ℤ k (powerSeriesIterate f (p ^ n)) -
    HahnSeries.single (1 : ℤ) 1).order - 1
  have hstrict : StrictMono d := strictMono_primePowerIterate_ramification p f hf hlinear hinfinite
  have hlower : ∀ n : ℕ, (n : ℤ) + 1 ≤ d n := by
    intro n
    induction n with
    | zero =>
      have := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite (p ^ 0)
        (pow_pos (Fact.out : p.Prime).pos _)
      dsimp only [d]
      omega
    | succ n ih =>
      have hstep : d n < d (n + 1) := hstrict (Nat.lt_succ_self n)
      change (((n + 1 : ℕ) : ℤ) + 1) ≤ d (n + 1)
      push_cast
      omega
  apply tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge b
  exact (eventually_ge_atTop N).mono fun n hn ↦ calc
    b ≤ (N : ℤ) := hN
    _ ≤ (n : ℤ) := by exact_mod_cast hn
    _ ≤ d n := by have := hlower n; omega

end LaurentSeries
