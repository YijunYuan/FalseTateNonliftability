module

public import FalseTateNonliftability.LaurentSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Laurent displacement and first-order remainders

Integer powers are taken in the actual unit group. Finite Laurent truncations
pass their monomial estimates to canonical continuous substitution in the
named order topology, retaining every negative exponent.

The leading coefficient and characteristic-prime exact order are computed
on the same Laurent series. Power-series inputs have a stronger remainder
that is actually divisible by the square of the displacement with a
power-series quotient, yielding the strict-order comparison formula.

This proves blueprint lemmas `nl:laurent-displacement` and `nl:laurent-taylor`.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

open Filter
open scoped Topology

variable {R : Type*} [CommRing R]

/-- The first-order integer-power remainder is divisible by the square of
the unit difference in the original ring, including all negative powers. -/
theorem sq_sub_one_dvd_unit_zpow_sub_firstOrder (u : Rˣ) (j : ℤ) :
    ((u : R) - 1) ^ 2 ∣ (↑(u ^ j) : R) - 1 - (j : R) * ((u : R) - 1) := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n _ =>
    have hpos : ((u : R) - 1) ^ 2 ∣
        (u : R) ^ (n + 1) - 1 - ((n + 1 : ℕ) : R) * ((u : R) - 1) := by
      convert sq_dvd_add_pow_sub_sub ((u : R) - 1) 1 (n + 1) using 1
      ring
    change ((u : R) - 1) ^ 2 ∣
      (↑(u ^ ((n + 1 : ℕ) : ℤ)) : R) - 1 - (((n + 1 : ℕ) : ℤ) : R) * ((u : R) - 1)
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast] using hpos
  | pred n ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨(↑(u⁻¹) : R) * (v - ((-(n : ℤ) - 1 : ℤ) : R)), ?_⟩
    rw [zpow_sub_one, Units.val_mul]
    push_cast
    have hunit : (u : R) * (↑(u⁻¹) : R) = 1 := u.mul_inv
    push_cast at hv
    linear_combination (↑(u⁻¹) : R) * hv +
      (1 + ((-(n : R) - 1) * ((u : R) - 1))) * hunit

/-- Every actual integer-power difference is divisible by the original unit
difference. This holds in the original power-series ring when it is the coefficient ring. -/
theorem sub_one_dvd_unit_zpow_sub_one (u : Rˣ) (j : ℤ) :
    (u : R) - 1 ∣ (↑(u ^ j) : R) - 1 := by
  obtain ⟨v, hv⟩ := sq_sub_one_dvd_unit_zpow_sub_firstOrder u j
  refine ⟨(j : R) + ((u : R) - 1) * v, ?_⟩
  linear_combination hv

/-- Embedded power series have no negative coefficients. -/
theorem ofPowerSeries_mem_orderAddSubgroup_zero (P : PowerSeries R) :
    HahnSeries.ofPowerSeries ℤ R P ∈ orderAddSubgroup 0 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [PowerSeries.coeff_coe, ite_eq_left hj]

/-- Finite sums preserve a common lower coefficient bound on the actual carrier. -/
theorem sum_mem_orderAddSubgroup {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries R)
    (m : ℤ) (hf : ∀ i ∈ s, f i ∈ orderAddSubgroup m) :
    ∑ i ∈ s, f i ∈ orderAddSubgroup m := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero (fun i hi ↦ (mem_orderAddSubgroup_iff_coeff m (f i)).mp (hf i hi) j hj)

/-- Every actual order subgroup is closed in the explicitly named topology. -/
theorem isClosed_orderAddSubgroup (m : ℤ) :
    @IsClosed (LaurentSeries R) (orderTopology R) (orderAddSubgroup (R := R) m) := by
  let := orderTopology R
  let := orderTopology_isTopologicalAddGroup (R := R)
  exact (orderAddSubgroup m).isClosed_of_isOpen (isOpen_orderAddSubgroup m)

/-- A specified first term and higher tail give the corresponding lower bound. -/
theorem mem_orderAddSubgroup_of_sub_single_mem (f : LaurentSeries R) (m : ℤ) (b : R)
    (hf : f - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) : f ∈ orderAddSubgroup m := by
  have htail := orderAddSubgroup_antitone (show m ≤ m + 1 by omega) hf
  have hsum := (orderAddSubgroup m).add_mem htail
    (show HahnSeries.single m b ∈ orderAddSubgroup m from HahnSeries.orderTop_single_le)
  simpa only [sub_add_cancel] using hsum

/-- Removing the actual lowest coefficient leaves a strictly higher tail. -/
theorem sub_leadingTerm_mem_orderAddSubgroup (f : LaurentSeries R) :
    f - HahnSeries.single f.order (f.coeff f.order) ∈ orderAddSubgroup (f.order + 1) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [HahnSeries.coeff_sub]
  by_cases heq : j = f.order
  · subst j
    rw [HahnSeries.coeff_single_same, sub_self]
  · rw [HahnSeries.coeff_eq_zero_of_lt_order (by omega), HahnSeries.coeff_single_of_ne heq, sub_self]

/-- A nonzero specified first coefficient computes the actual Laurent order. -/
theorem order_eq_of_sub_single_mem (f : LaurentSeries R) (m : ℤ) (b : R) (hb : b ≠ 0)
    (hf : f - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) : f.order = m := by
  have hc := (mem_orderAddSubgroup_iff_coeff (m + 1) _).mp hf m (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
  have hn : f.coeff m ≠ 0 := by rw [hc]; exact hb
  have ht : f.orderTop = (m : WithTop ℤ) := le_antisymm
    (HahnSeries.orderTop_le_of_coeff_ne_zero hn) (mem_orderAddSubgroup_of_sub_single_mem f m b hf)
  exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero (HahnSeries.ne_zero_of_coeff_ne_zero hn)).trans ht

private theorem nonzero_and_order_eq_of_orderTop_eq (f : LaurentSeries R) (m : ℤ)
    (hf : f.orderTop = (m : WithTop ℤ)) : f ≠ 0 ∧ f.order = m := by
  have hne : f ≠ 0 := HahnSeries.orderTop_ne_top.mp (by rw [hf]; exact WithTop.coe_ne_top)
  exact ⟨hne, by exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero hne).trans hf⟩

section Field

variable {k : Type*} [Field k]

local instance taylorZeroSpanIsMaximal : (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- Multiplying the variable by an actual principal power-series unit gives
an actual admissible Laurent coordinate. -/
theorem principalUnitCoordinate_isAdmissible (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) :
    IsAdmissible (0 : k)
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k)) := by
  have hzero : (PowerSeries.X * (u : PowerSeries k)).constantCoeff = 0 := by simp
  have hlinear : IsUnit ((PowerSeries.X * (u : PowerSeries k)).coeff 1) := by
    change IsUnit ((PowerSeries.X * (u : PowerSeries k)).coeff (0 + 1))
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hu]
    exact isUnit_one
  simpa only [map_mul, HahnSeries.ofPowerSeries_X] using
    isAdmissible_ofPowerSeries (0 : k) _ hzero hlinear

/-- On every integer monomial, actual substitution by `T*u` multiplies by
the actual integer power of the original power-series unit. -/
theorem subst_principalUnit_single (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) (j : ℤ) (b : k) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) (HahnSeries.single j b) =
      HahnSeries.single j b * HahnSeries.ofPowerSeries ℤ k (↑(u ^ j) : PowerSeries k) := by
  let F := subst 0 IsNilpotent.zero
    (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
    (principalUnitCoordinate_isAdmissible u hu)
  have hX : F (HahnSeries.single (1 : ℤ) 1) =
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k) :=
    subst_X 0 IsNilpotent.zero _ (principalUnitCoordinate_isAdmissible u hu)
  have hneg : F (HahnSeries.single (-1 : ℤ) 1) =
      HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (↑(u⁻¹) : PowerSeries k) := by
    apply inv_unique (x := F (HahnSeries.single (1 : ℤ) 1))
    · rw [← map_mul]
      simp
    · rw [hX]
      calc
        _ = (HahnSeries.single (1 : ℤ) 1 * HahnSeries.single (-1 : ℤ) 1) *
            HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) * ↑(u⁻¹)) := by rw [map_mul]; ring
        _ = 1 := by simp
  have hone (j : ℤ) : F (HahnSeries.single j 1) =
      HahnSeries.single j 1 * HahnSeries.ofPowerSeries ℤ k (↑(u ^ j) : PowerSeries k) := by
    induction j using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [show (HahnSeries.single ((n : ℤ) + 1) 1 : LaurentSeries k) =
          HahnSeries.single (n : ℤ) 1 * HahnSeries.single (1 : ℤ) 1 by simp,
        map_mul, ih, hX, zpow_add, zpow_one, Units.val_mul, map_mul]
      ring
    | pred n ih =>
      rw [show (HahnSeries.single (-(n : ℤ) - 1) 1 : LaurentSeries k) =
          HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.single (-1 : ℤ) 1 by simp [sub_eq_add_neg],
        map_mul, ih, hneg, zpow_sub_one, Units.val_mul, map_mul]
      ring
  have hC : F (HahnSeries.C b) = HahnSeries.C b := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using F.commutes b
  have hb : (HahnSeries.single j b : LaurentSeries k) = HahnSeries.C b * HahnSeries.single j 1 := by
    simp
  change F (HahnSeries.single j b) = _
  rw [hb, map_mul, hC, hone]
  ring

/-- The actual monomial first-order remainder is the embedded original
power-series unit remainder, multiplied by the original integer monomial. -/
theorem subst_principalUnit_single_sub_firstOrder (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) (j : ℤ) (b : k) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) (HahnSeries.single j b) - HahnSeries.single j b -
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1)) *
        derivative k (HahnSeries.single j b) =
      HahnSeries.single j b * HahnSeries.ofPowerSeries ℤ k
        ((↑(u ^ j) : PowerSeries k) - 1 - (j : PowerSeries k) * ((u : PowerSeries k) - 1)) := by
  have hcast : (j : LaurentSeries k) = HahnSeries.C (j : k) :=
    (map_intCast (HahnSeries.C : k →+* LaurentSeries k) j).symm
  have hlin : (HahnSeries.single (1 : ℤ) 1 : LaurentSeries k) *
      derivative k (HahnSeries.single j b) = HahnSeries.single j b * (j : LaurentSeries k) := by
    simp only [derivative_single, hcast, HahnSeries.C_apply, HahnSeries.single_mul_single,
      show (1 : ℤ) + (j - 1) = j by omega, mul_one, add_zero, mul_comm]
  rw [subst_principalUnit_single u hu j b]
  simp only [map_sub, map_one, map_mul, map_intCast]
  linear_combination -(HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k) - 1) * hlin

/-- Each integer monomial has the genuine displacement lower bound, with
its auxiliary factor still in the original power-series ring. -/
theorem subst_principalUnit_single_sub_mem (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) (d : ℤ)
    (hd : HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1) ∈ orderAddSubgroup d)
    (j : ℤ) (b : k) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) (HahnSeries.single j b) - HahnSeries.single j b ∈
      orderAddSubgroup (j + d) := by
  obtain ⟨V, hV⟩ := sub_one_dvd_unit_zpow_sub_one u j
  have heq : subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) (HahnSeries.single j b) - HahnSeries.single j b =
      HahnSeries.single j b * HahnSeries.ofPowerSeries ℤ k ((↑(u ^ j) : PowerSeries k) - 1) := by
    rw [subst_principalUnit_single u hu j b]
    simp only [map_sub, map_one]
    ring
  rw [heq, hV, map_mul]
  have hfactor := mul_mem_orderAddSubgroup hd (ofPowerSeries_mem_orderAddSubgroup_zero V)
  simpa only [add_zero] using mul_mem_orderAddSubgroup
    (show HahnSeries.single j b ∈ orderAddSubgroup j from HahnSeries.orderTop_single_le) hfactor

/-- Each integer monomial has the controlled Taylor remainder, including
negative degrees and zero coefficients. -/
theorem subst_principalUnit_single_taylor_mem (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) (d : ℤ)
    (hd : HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1) ∈ orderAddSubgroup d)
    (j : ℤ) (b : k) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) (HahnSeries.single j b) - HahnSeries.single j b -
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1)) *
        derivative k (HahnSeries.single j b) ∈ orderAddSubgroup (j + 2 * d) := by
  obtain ⟨V, hV⟩ := sq_sub_one_dvd_unit_zpow_sub_firstOrder u j
  rw [subst_principalUnit_single_sub_firstOrder u hu j b, hV, map_mul, map_pow, pow_two]
  have hfactor := mul_mem_orderAddSubgroup (mul_mem_orderAddSubgroup hd hd)
    (ofPowerSeries_mem_orderAddSubgroup_zero V)
  have hprod := mul_mem_orderAddSubgroup
    (show HahnSeries.single j b ∈ orderAddSubgroup j from HahnSeries.orderTop_single_le) hfactor
  simpa only [add_zero, ← two_mul] using hprod

/-- Actual Laurent displacement raises every integer support lower bound by
`d`. Finite truncations retain all negative degrees, and closedness passes
their proved bounds to the actual substitution limit. -/
theorem subst_principalUnit_sub_mem (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) (d : ℤ)
    (hd : HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1) ∈ orderAddSubgroup d)
    (m : ℤ) (f : LaurentSeries k) (hf : f ∈ orderAddSubgroup m) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) f - f ∈ orderAddSubgroup (m + d) := by
  let := orderTopology k
  let := orderTopology_isTopologicalRing (R := k)
  let F := subst 0 IsNilpotent.zero
    (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
    (principalUnitCoordinate_isAdmissible u hu)
  have hfinite (n : ℕ) : F (HahnSeries.truncLT (n : ℤ) f) - HahnSeries.truncLT (n : ℤ) f ∈
      orderAddSubgroup (m + d) := by
    classical
    rw [truncLT_eq_sum_Ico, map_sum, ← Finset.sum_sub_distrib]
    apply sum_mem_orderAddSubgroup
    intro j _
    by_cases hj : m ≤ j
    · exact orderAddSubgroup_antitone (by omega)
        (subst_principalUnit_single_sub_mem u hu d hd j (f.coeff j))
    · have hz := (mem_orderAddSubgroup_iff_coeff m f).mp hf j (lt_of_not_ge hj)
      simp only [hz, map_zero, sub_self, zero_mem]
  have ht := (((continuous_subst 0 IsNilpotent.zero _
    (principalUnitCoordinate_isAdmissible u hu)).sub continuous_id).tendsto f).comp
      (tendsto_truncLT_orderTopology f)
  exact (isClosed_orderAddSubgroup (m + d)).mem_of_tendsto ht (Eventually.of_forall hfinite)

/-- The controlled Laurent first-order remainder for the actual substitution
by `T*u`, with arbitrary integer input order and no assumed Taylor identity. -/
theorem subst_principalUnit_taylor_mem (u : (PowerSeries k)ˣ)
    (hu : PowerSeries.constantCoeff (u : PowerSeries k) = 1) (d : ℤ)
    (hd : HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1) ∈ orderAddSubgroup d)
    (m : ℤ) (f : LaurentSeries k) (hf : f ∈ orderAddSubgroup m) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
        (principalUnitCoordinate_isAdmissible u hu) f - f -
      (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1)) *
        derivative k f ∈ orderAddSubgroup (m + 2 * d) := by
  let := orderTopology k
  let := orderTopology_isTopologicalRing (R := k)
  let F := subst 0 IsNilpotent.zero
    (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k))
    (principalUnitCoordinate_isAdmissible u hu)
  let δ := HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1)
  have hfinite (n : ℕ) : F (HahnSeries.truncLT (n : ℤ) f) - HahnSeries.truncLT (n : ℤ) f -
      δ * derivative k (HahnSeries.truncLT (n : ℤ) f) ∈ orderAddSubgroup (m + 2 * d) := by
    classical
    rw [truncLT_eq_sum_Ico, map_sum, map_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply sum_mem_orderAddSubgroup
    intro j _
    by_cases hj : m ≤ j
    · exact orderAddSubgroup_antitone (by omega)
        (subst_principalUnit_single_taylor_mem u hu d hd j (f.coeff j))
    · have hz := (mem_orderAddSubgroup_iff_coeff m f).mp hf j (lt_of_not_ge hj)
      simp only [hz, map_zero, sub_self, mul_zero, zero_mem]
  have hc : Continuous (fun x : LaurentSeries k ↦ F x - x - δ * derivative k x) :=
    ((continuous_subst 0 IsNilpotent.zero _ (principalUnitCoordinate_isAdmissible u hu)).sub
      continuous_id).sub (continuous_const.mul continuous_derivative)
  exact (isClosed_orderAddSubgroup (m + 2 * d)).mem_of_tendsto
    ((hc.tendsto f).comp (tendsto_truncLT_orderTopology f)) (Eventually.of_forall hfinite)

/-- Every actual Laurent coordinate sufficiently close to the variable is
`T*u` for an actual principal unit of the original power-series ring. -/
theorem exists_principalUnitCoordinate_of_sub_mem (g : LaurentSeries k) (d : ℤ) (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) :
    ∃ u : (PowerSeries k)ˣ, PowerSeries.constantCoeff (u : PowerSeries k) = 1 ∧
      g = HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (u : PowerSeries k) ∧
      HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1) ∈ orderAddSubgroup d := by
  let z := HahnSeries.single (-1 : ℤ) 1 * (g - HahnSeries.single (1 : ℤ) 1)
  have hz : z ∈ orderAddSubgroup d := by
    simpa only [show (-1 : ℤ) + (d + 1) = d by omega] using
      mul_mem_orderAddSubgroup
        (show (HahnSeries.single (-1 : ℤ) 1 : LaurentSeries k) ∈ orderAddSubgroup (-1) from
          HahnSeries.orderTop_single_le) hg
  let Z := PowerSeries.mk (fun n : ℕ ↦ z.coeff n)
  have hZ : HahnSeries.ofPowerSeries ℤ k Z = z :=
    ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero z
      (orderAddSubgroup_antitone (show 0 ≤ d by omega) hz)
  have hZ0 : Z.constantCoeff = 0 := by
    simpa only [Z, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, Nat.cast_zero] using
      (mem_orderAddSubgroup_iff_coeff d z).mp hz 0 (by omega)
  have hU0 : PowerSeries.constantCoeff (1 + Z) = 1 := by rw [map_add, map_one, hZ0, add_zero]
  have hU : IsUnit (1 + Z) := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hU0]; exact isUnit_one)
  refine ⟨hU.unit, ?_, ?_, ?_⟩
  · rw [hU.unit_spec]
    exact hU0
  · simp only [hU.unit_spec, map_add, map_one, hZ]
    have hT : (HahnSeries.single (1 : ℤ) 1 : LaurentSeries k) *
        HahnSeries.single (-1 : ℤ) 1 = 1 := by simp
    dsimp only [z]
    linear_combination -(g - HahnSeries.single (1 : ℤ) 1) * hT
  · simpa only [hU.unit_spec, add_sub_cancel_left, hZ] using hz

/-- Admissibility of an actual near-identity Laurent coordinate follows from
the actual support bound; it is not an additional certificate. -/
theorem isAdmissible_of_sub_variable_mem (g : LaurentSeries k) (d : ℤ) (hd : 1 ≤ d)
    (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1)) : IsAdmissible (0 : k) g := by
  obtain ⟨u, hu, hgu, _⟩ := exists_principalUnitCoordinate_of_sub_mem g d hd hg
  rw [hgu]
  exact principalUnitCoordinate_isAdmissible u hu

/-- Actual displacement for every near-identity Laurent coordinate and every
integer lower support bound. -/
theorem subst_sub_mem_orderAddSubgroup (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d) (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1))
    (m : ℤ) (f : LaurentSeries k) (hf : f ∈ orderAddSubgroup m) :
    subst 0 IsNilpotent.zero g hG f - f ∈ orderAddSubgroup (m + d) := by
  obtain ⟨u, hu, hgu, hunit⟩ := exists_principalUnitCoordinate_of_sub_mem g d hd hg
  simpa only [hgu] using subst_principalUnit_sub_mem u hu d hunit m f hf

/-- The actual first-order Laurent expansion with the controlled remainder
`m + 2*d`, including arbitrary negative Laurent order. -/
theorem subst_taylor_mem_orderAddSubgroup (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d) (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1))
    (m : ℤ) (f : LaurentSeries k) (hf : f ∈ orderAddSubgroup m) :
    subst 0 IsNilpotent.zero g hG f - f -
      (g - HahnSeries.single (1 : ℤ) 1) * derivative k f ∈ orderAddSubgroup (m + 2 * d) := by
  obtain ⟨u, hu, hgu, hunit⟩ := exists_principalUnitCoordinate_of_sub_mem g d hd hg
  have hδ : g - HahnSeries.single (1 : ℤ) 1 =
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k ((u : PowerSeries k) - 1) := by
    simp only [hgu, map_sub, map_one]
    ring
  rw [hδ]
  simpa only [hgu] using subst_principalUnit_taylor_mem u hu d hunit m f hf

/-- The actual displacement leading term, valid for every integer Laurent
exponent. The tail bounds are coefficient bounds on the actual series. -/
theorem subst_sub_leadingTerm_mem (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d) (α : k)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + 2))
    (x : LaurentSeries k) (m : ℤ) (b : k)
    (hx : x - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) :
    subst 0 IsNilpotent.zero g hG x - x -
      HahnSeries.single (m + d) ((m : k) * α * b) ∈ orderAddSubgroup (m + d + 1) := by
  let δ := g - HahnSeries.single (1 : ℤ) 1
  have hδ : δ ∈ orderAddSubgroup (d + 1) :=
    mem_orderAddSubgroup_of_sub_single_mem δ (d + 1) α
      (by simpa only [show d + 1 + 1 = d + 2 by omega] using hg)
  have hxlow := mem_orderAddSubgroup_of_sub_single_mem x m b hx
  have hTaylor := subst_taylor_mem_orderAddSubgroup g hG d hd hδ m x hxlow
  have hTaylor' : subst 0 IsNilpotent.zero g hG x - x - δ * derivative k x ∈
      orderAddSubgroup (m + d + 1) := orderAddSubgroup_antitone (by omega) hTaylor
  have hDx : derivative k x - derivative k (HahnSeries.single m b) ∈ orderAddSubgroup m := by
    simpa only [map_sub, add_sub_cancel_right] using
      derivative_mem_orderAddSubgroup (m + 1) (x - HahnSeries.single m b) hx
  have hfirst : δ * (derivative k x - derivative k (HahnSeries.single m b)) ∈
      orderAddSubgroup (m + d + 1) := by
    simpa only [show d + 1 + m = m + d + 1 by omega] using mul_mem_orderAddSubgroup hδ hDx
  have hsecond : (δ - HahnSeries.single (d + 1) α) * derivative k (HahnSeries.single m b) ∈
      orderAddSubgroup (m + d + 1) := by
    have hDm := derivative_mem_orderAddSubgroup m (HahnSeries.single m b)
      (show HahnSeries.single m b ∈ orderAddSubgroup m from HahnSeries.orderTop_single_le)
    simpa only [show d + 2 + (m - 1) = m + d + 1 by omega] using mul_mem_orderAddSubgroup hg hDm
  have hlead : HahnSeries.single (d + 1) α * derivative k (HahnSeries.single m b) =
      HahnSeries.single (m + d) ((m : k) * α * b) := by
    rw [derivative_single, HahnSeries.single_mul_single, show d + 1 + (m - 1) = m + d by omega]
    congr 1
    ring
  have hsum := (orderAddSubgroup (m + d + 1)).add_mem hTaylor'
    ((orderAddSubgroup (m + d + 1)).add_mem hfirst hsecond)
  convert hsum using 1
  rw [← hlead]
  ring

/-- When the input order is prime to the characteristic, its actual leading
displacement coefficient is nonzero and the displacement order is exact. -/
theorem order_subst_sub_eq_of_not_dvd (p : ℕ) [CharP k p]
    (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g) (d : ℤ) (hd : 1 ≤ d)
    (α : k) (hα : α ≠ 0)
    (hg : g - HahnSeries.single (1 : ℤ) 1 - HahnSeries.single (d + 1) α ∈ orderAddSubgroup (d + 2))
    (x : LaurentSeries k) (hx : x ≠ 0) (hm : ¬ (p : ℤ) ∣ x.order) :
    (subst 0 IsNilpotent.zero g hG x - x).order = x.order + d := by
  apply order_eq_of_sub_single_mem _ _ ((x.order : k) * α * x.coeff x.order)
  · exact mul_ne_zero (mul_ne_zero (mt (CharP.intCast_eq_zero_iff k p x.order).mp hm) hα)
      (HahnSeries.coeff_order_eq_zero.not.mpr hx)
  · exact subst_sub_leadingTerm_mem g hG d hd α hg x x.order (x.coeff x.order)
      (sub_leadingTerm_mem_orderAddSubgroup x)

/-- Constants cancel from actual power-series displacement, giving the stronger
bound `d + 1`; no invertibility of the input power series is needed. -/
theorem subst_ofPowerSeries_sub_mem (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d) (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1))
    (U : PowerSeries k) :
    subst 0 IsNilpotent.zero g hG (HahnSeries.ofPowerSeries ℤ k U) -
      HahnSeries.ofPowerSeries ℤ k U ∈ orderAddSubgroup (d + 1) := by
  let F := subst 0 IsNilpotent.zero g hG
  let x := HahnSeries.ofPowerSeries ℤ k U - HahnSeries.C U.constantCoeff
  have hx : x ∈ orderAddSubgroup 1 := by
    rw [mem_orderAddSubgroup_iff_coeff]
    intro j hj
    change (HahnSeries.ofPowerSeries ℤ k U - HahnSeries.C U.constantCoeff).coeff j = 0
    rw [HahnSeries.coeff_sub, HahnSeries.C_apply]
    by_cases hj0 : j < 0
    · rw [PowerSeries.coeff_coe, ite_eq_left hj0, HahnSeries.coeff_single_of_ne (ne_of_lt hj0), sub_self]
    · have hjz : j = 0 := by omega
      subst j
      simp only [show (0 : ℤ) = (0 : ℕ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, HahnSeries.coeff_single_same, sub_self]
  have hb := subst_sub_mem_orderAddSubgroup g hG d hd hg 1 x hx
  have hC : F (HahnSeries.C U.constantCoeff) = HahnSeries.C U.constantCoeff := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using F.commutes U.constantCoeff
  have heq : F x - x = F (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U := by
    dsimp only [x]
    rw [map_sub, hC]
    abel
  change F x - x ∈ orderAddSubgroup (1 + d) at hb
  rw [heq] at hb
  simpa only [add_comm 1 d] using hb

/-- Removing the constant and linear terms sharpens the actual power-series
Taylor remainder to `2*d + 2`. This is stronger than the arbitrary Laurent bound. -/
theorem subst_ofPowerSeries_taylor_mem (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d) (hg : g - HahnSeries.single (1 : ℤ) 1 ∈ orderAddSubgroup (d + 1))
    (U : PowerSeries k) :
    subst 0 IsNilpotent.zero g hG (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U -
      (g - HahnSeries.single (1 : ℤ) 1) * derivative k (HahnSeries.ofPowerSeries ℤ k U) ∈
        orderAddSubgroup (2 * d + 2) := by
  let F := subst 0 IsNilpotent.zero g hG
  let δ := g - HahnSeries.single (1 : ℤ) 1
  let x := HahnSeries.ofPowerSeries ℤ k U - HahnSeries.C U.constantCoeff -
    HahnSeries.single (1 : ℤ) (U.coeff 1)
  have hx : x ∈ orderAddSubgroup 2 := by
    rw [mem_orderAddSubgroup_iff_coeff]
    intro j hj
    dsimp only [x]
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_sub, HahnSeries.C_apply]
    by_cases hj0 : j < 0
    · rw [PowerSeries.coeff_coe, ite_eq_left hj0, HahnSeries.coeff_single_of_ne (ne_of_lt hj0),
        HahnSeries.coeff_single_of_ne (by omega : j ≠ 1), sub_self, sub_self]
    · have hjz : j = 0 ∨ j = 1 := by omega
      rcases hjz with rfl | rfl
      · simp [PowerSeries.coeff_coe]
      · simp [PowerSeries.coeff_coe]
  have ht := subst_taylor_mem_orderAddSubgroup g hG d hd hg 2 x hx
  have hC (b : k) : F (HahnSeries.C b) = HahnSeries.C b := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using F.commutes b
  have hrep : (HahnSeries.single (1 : ℤ) (U.coeff 1) : LaurentSeries k) =
      HahnSeries.C (U.coeff 1) * HahnSeries.single (1 : ℤ) 1 := by simp
  have hlinear : F (HahnSeries.single (1 : ℤ) (U.coeff 1)) = HahnSeries.C (U.coeff 1) * g := by
    rw [hrep, map_mul, hC]
    exact congrArg (HahnSeries.C (U.coeff 1) * ·) (subst_X 0 IsNilpotent.zero g hG)
  have hDlinear : derivative k (HahnSeries.single (1 : ℤ) (U.coeff 1)) = HahnSeries.C (U.coeff 1) := by
    simp [HahnSeries.C_apply]
  have heq : F x - x - δ * derivative k x =
      F (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U -
        δ * derivative k (HahnSeries.ofPowerSeries ℤ k U) := by
    dsimp only [x]
    simp only [map_sub]
    rw [hC, hlinear, derivative_C, hDlinear, hrep]
    dsimp only [δ]
    ring
  change F x - x - δ * derivative k x ∈ orderAddSubgroup (2 + 2 * d) at ht
  rw [heq] at ht
  simpa only [add_comm 2 (2 * d)] using ht

/-- The stronger power-series Taylor remainder has an actual power-series
factor after division by the square of the displacement. Division is carried
out in the canonical Laurent field and its nonnegative support is proved. -/
theorem exists_powerSeries_taylor_remainder (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d)
    (hg : (g - HahnSeries.single (1 : ℤ) 1).orderTop = ((d + 1 : ℤ) : WithTop ℤ))
    (U : PowerSeries k) :
    ∃ V : PowerSeries k,
      subst 0 IsNilpotent.zero g hG (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U -
        (g - HahnSeries.single (1 : ℤ) 1) * HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U) =
      (g - HahnSeries.single (1 : ℤ) 1) ^ 2 * HahnSeries.ofPowerSeries ℤ k V := by
  let δ := g - HahnSeries.single (1 : ℤ) 1
  let A := subst 0 IsNilpotent.zero g hG (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U -
    δ * HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)
  have hA : A ∈ orderAddSubgroup (2 * d + 2) := by
    simpa only [derivative_ofPowerSeries] using subst_ofPowerSeries_taylor_mem g hG d hd hg.ge U
  obtain ⟨hδne, hδorder⟩ := nonzero_and_order_eq_of_orderTop_eq δ (d + 1) hg
  let q := A / δ ^ 2
  have hprod : δ ^ 2 * q = A := by
    dsimp only [q]
    exact mul_div_cancel₀ A (pow_ne_zero 2 hδne)
  have hq : q ∈ orderAddSubgroup 0 := by
    by_cases hq0 : q = 0
    · simpa only [hq0] using (orderAddSubgroup (R := k) 0).zero_mem
    have hAne : A ≠ 0 := fun h ↦ mul_ne_zero (pow_ne_zero 2 hδne) hq0 (hprod.trans h)
    have hAorder : 2 * d + 2 ≤ A.order := by
      change ((2 * d + 2 : ℤ) : WithTop ℤ) ≤ A.orderTop at hA
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hAne] at hA
      exact_mod_cast hA
    have hδpow : (δ ^ 2).order = 2 * (d + 1) := by
      rw [pow_two, HahnSeries.order_mul hδne hδne, hδorder]
      ring
    have ho := congrArg HahnSeries.order hprod
    rw [HahnSeries.order_mul (pow_ne_zero 2 hδne) hq0, hδpow] at ho
    exact orderAddSubgroup_antitone (show 0 ≤ q.order by omega) (mem_orderAddSubgroup_order q)
  refine ⟨PowerSeries.mk (fun n : ℕ ↦ q.coeff n), ?_⟩
  rw [ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero q hq]
  exact hprod.symm

/-- If the nonzero input derivative has order less than the displacement,
the first-order term is strictly below the proved power-series remainder,
so the actual displacement order is the sum of the two original orders. -/
theorem order_subst_ofPowerSeries_sub_eq (g : LaurentSeries k) (hG : IsAdmissible (0 : k) g)
    (d : ℤ) (hd : 1 ≤ d)
    (hg : (g - HahnSeries.single (1 : ℤ) 1).orderTop = ((d + 1 : ℤ) : WithTop ℤ))
    (U : PowerSeries k) (hU : HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U) ≠ 0)
    (hsmall : (HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)).order < d + 1) :
    (subst 0 IsNilpotent.zero g hG (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U).order =
      d + 1 + (HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)).order := by
  let δ := g - HahnSeries.single (1 : ℤ) 1
  let D := HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative U)
  change D.order < d + 1 at hsmall
  let B := subst 0 IsNilpotent.zero g hG (HahnSeries.ofPowerSeries ℤ k U) - HahnSeries.ofPowerSeries ℤ k U
  obtain ⟨V, hV⟩ := exists_powerSeries_taylor_remainder g hG d hd hg U
  change B - δ * D = δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V at hV
  have hB : B = δ * D + δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V := by linear_combination hV
  obtain ⟨hδne, hδorder⟩ := nonzero_and_order_eq_of_orderTop_eq δ (d + 1) hg
  have hLne : δ * D ≠ 0 := mul_ne_zero hδne hU
  have hLorder : (δ * D).order = d + 1 + D.order := by rw [HahnSeries.order_mul hδne hU, hδorder]
  have hR : δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V ∈ orderAddSubgroup (2 * d + 2) := by
    simpa only [pow_two, add_zero, show d + 1 + (d + 1) = 2 * d + 2 by omega] using
      mul_mem_orderAddSubgroup (mul_mem_orderAddSubgroup hg.ge hg.ge)
        (ofPowerSeries_mem_orderAddSubgroup_zero V)
  have hlt : (δ * D).orderTop < (δ ^ 2 * HahnSeries.ofPowerSeries ℤ k V).orderTop := by
    calc
      (δ * D).orderTop = ((d + 1 + D.order : ℤ) : WithTop ℤ) := by
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hLne, hLorder]
      _ < ((2 * d + 2 : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : d + 1 + D.order < 2 * d + 2)
      _ ≤ _ := hR
  have hBtop : B.orderTop = ((d + 1 + D.order : ℤ) : WithTop ℤ) := by
    rw [hB, HahnSeries.orderTop_add_eq_left hlt, ← HahnSeries.order_eq_orderTop_of_ne_zero hLne, hLorder]
  exact (nonzero_and_order_eq_of_orderTop_eq B _ hBtop).2

end Field

end LaurentSeries
