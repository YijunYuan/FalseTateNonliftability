/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Derivative
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The `T`-adic topology on Laurent series over a commutative ring

Let `R` be a commutative ring. The additive subgroups `orderAddSubgroup m` of Laurent series
`f = O(T ^ m)` in `R((T))`, `m ∈ ℤ`, form a basis of neighborhoods of zero for a Hausdorff ring
topology on `R((T))`, also when `R` has nilpotent elements. A family converges for this topology if
and only if, for every `m`, its coefficients in all degrees below `m` are eventually those of the
limit. The truncations `∑_{j < n} f_j T ^ j` of `f` converge to `f`, so a continuous ring
homomorphism from `R((T))` to a Hausdorff ring is determined by its values on the constants and on
`T`. The derivative `d / dT` is continuous. Over a field `K`, the topology is the topology of the
`T`-adic valuation of `K((T))`.

## Main definitions

* `LaurentSeries.orderAddSubgroup m`: the additive subgroup of the series `f = O(T ^ m)`.
* `LaurentSeries.orderTopology R`: the `T`-adic topology on `R((T))`, a scoped instance in
  `LaurentSeries.OrderTopology`.

## Main results

* `LaurentSeries.OrderTopology.instIsTopologicalRing`, `LaurentSeries.OrderTopology.instT2Space`:
  the `T`-adic topology is a Hausdorff ring topology.
* `LaurentSeries.tendsto_orderTopology_iff`: convergence is eventual agreement of all
  coefficients below every bound.
* `LaurentSeries.tendsto_truncLT_orderTopology`: the truncations of `f` converge to `f`.
* `LaurentSeries.continuous_ringHom_ext`, `LaurentSeries.continuous_algHom_ext_X`: continuous
  homomorphisms from `R((T))` to a Hausdorff ring that agree on the constants and at `T` are
  equal.
* `LaurentSeries.continuous_derivative`: `d / dT` is continuous.
* `LaurentSeries.continuous_ofPowerSeries`: over a discrete ring, `R⟦T⟧ → R((T))` is continuous for
  the topology of coefficientwise convergence on `R⟦T⟧`.
* `LaurentSeries.orderTopology_eq_valued`: over a field, the `T`-adic topology is the topology of
  the valuation.

## Implementation details

Over a field `K`, Mathlib equips `LaurentSeries K` with the topology of its `T`-adic valuation
(`LaurentSeries.valued`), so `orderTopology R` is only a scoped instance, activated by
`open scoped LaurentSeries.OrderTopology`; it has high priority, so that it is also chosen over a
field when the scope is open. The two topologies on `LaurentSeries K` are equal
(`orderTopology_eq_valued`) but not definitionally equal: do not open the scope where the valued
topology of `LaurentSeries K` is used, and rewrite with `orderTopology_eq_valued` where the two
meet.
-/

@[expose] public section

namespace LaurentSeries

open Filter Set
open scoped Topology Pointwise

noncomputable section

variable {R : Type*} [CommRing R]

/-- The additive subgroup of Laurent series whose order is at least `m`. -/
def orderAddSubgroup (m : ℤ) : AddSubgroup (LaurentSeries R) where
  carrier := {f | (m : WithTop ℤ) ≤ f.orderTop}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    exact (le_min hf hg).trans HahnSeries.min_orderTop_le_orderTop_add
  neg_mem' := by
    intro f hf
    simpa only [Set.mem_ofPred_eq, HahnSeries.orderTop_neg] using hf

@[simp]
theorem mem_orderAddSubgroup (m : ℤ) (f : LaurentSeries R) :
    f ∈ orderAddSubgroup m ↔ (m : WithTop ℤ) ≤ f.orderTop := Iff.rfl

/-- `f = O(T ^ m)` if and only if all coefficients of `f` in degrees below `m` vanish. -/
theorem mem_orderAddSubgroup_iff_coeff (m : ℤ) (f : LaurentSeries R) :
    f ∈ orderAddSubgroup m ↔ ∀ j : ℤ, j < m → f.coeff j = 0 := by
  simpa only [mem_orderAddSubgroup, WithTop.coe_lt_coe] using
    (HahnSeries.le_orderTop_iff_forall (x := f) (i := (m : WithTop ℤ)))

theorem orderAddSubgroup_antitone : Antitone (orderAddSubgroup (R := R)) := by
  intro m n hmn f hf
  exact (WithTop.coe_le_coe.mpr hmn).trans hf

/-- If `f = O(T ^ m)` and `g = O(T ^ n)`, then `f g = O(T ^ (m + n))`. -/
theorem mul_mem_orderAddSubgroup {m n : ℤ} {f g : LaurentSeries R}
    (hf : f ∈ orderAddSubgroup m) (hg : g ∈ orderAddSubgroup n) :
    f * g ∈ orderAddSubgroup (m + n) := by
  change ((m + n : ℤ) : WithTop ℤ) ≤ (f * g).orderTop
  calc
    _ = (m : WithTop ℤ) + (n : WithTop ℤ) := WithTop.coe_add _ _
    _ ≤ f.orderTop + g.orderTop := add_le_add hf hg
    _ ≤ _ := HahnSeries.orderTop_add_le_mul

/-- Every Laurent series `f` is `O(T ^ v(f))`, also for `f = 0`, where `v(0) = 0`. -/
theorem mem_orderAddSubgroup_order (f : LaurentSeries R) :
    f ∈ orderAddSubgroup f.order := by
  by_cases hf : f = 0
  · simp [hf]
  · change (f.order : WithTop ℤ) ≤ f.orderTop
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hf).le

theorem one_mem_orderAddSubgroup_zero : (1 : LaurentSeries R) ∈ orderAddSubgroup 0 := by
  rw [← HahnSeries.single_zero_one]
  exact HahnSeries.orderTop_single_le

/-- If `f = O(T ^ m)`, then `f ^ n = O(T ^ (n m))`. -/
theorem pow_mem_orderAddSubgroup {f : LaurentSeries R} {m : ℤ} (hf : f ∈ orderAddSubgroup m)
    (n : ℕ) : f ^ n ∈ orderAddSubgroup (n * m) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Nat.cast_zero, zero_mul] using one_mem_orderAddSubgroup_zero
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ]
    exact mul_mem_orderAddSubgroup ih hf

/-- If `f - 1 = O(T ^ m)` with `m ≥ 0`, then `f ^ n - 1 = O(T ^ m)`. -/
theorem pow_sub_one_mem_orderAddSubgroup {f : LaurentSeries R} {m : ℤ} (hm : 0 ≤ m)
    (hf : f - 1 ∈ orderAddSubgroup m) (n : ℕ) : f ^ n - 1 ∈ orderAddSubgroup m := by
  have hf0 : f ∈ orderAddSubgroup 0 := by
    simpa only [sub_add_cancel] using
      add_mem (orderAddSubgroup_antitone hm hf) one_mem_orderAddSubgroup_zero
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show f ^ n * f - 1 = (f ^ n - 1) * f + (f - 1) by ring]
    exact add_mem (by simpa only [add_zero] using mul_mem_orderAddSubgroup ih hf0) hf

/-- The subgroups `orderAddSubgroup m` form a basis of neighborhoods of zero of a ring topology. -/
theorem orderRingSubgroupsBasis : RingSubgroupsBasis (orderAddSubgroup (R := R)) := by
  apply RingSubgroupsBasis.of_comm
  · intro m n
    refine ⟨max m n, ?_⟩
    intro f hf
    exact ⟨orderAddSubgroup_antitone (le_max_left _ _) hf,
      orderAddSubgroup_antitone (le_max_right _ _) hf⟩
  · intro m
    refine ⟨max m 0, ?_⟩
    rintro _ ⟨f, hf, g, hg, rfl⟩
    apply orderAddSubgroup_antitone (show m ≤ max m 0 + max m 0 by omega)
    exact mul_mem_orderAddSubgroup hf hg
  · intro f m
    refine ⟨m - f.order, ?_⟩
    intro g hg
    have hprod := mul_mem_orderAddSubgroup (mem_orderAddSubgroup_order f) hg
    have hindex : f.order + (m - f.order) = m := by omega
    simpa only [hindex, Set.mem_preimage, SetLike.mem_coe] using hprod

/-- The `T`-adic topology on `R((T))`: the subgroups `orderAddSubgroup m` form a basis of
neighborhoods of zero. -/
@[instance_reducible]
def orderTopology (R : Type*) [CommRing R] : TopologicalSpace (LaurentSeries R) :=
  (orderRingSubgroupsBasis (R := R)).topology

namespace OrderTopology

/-- The `T`-adic topology on `R((T))`. -/
scoped instance (priority := high) instTopologicalSpace : TopologicalSpace (LaurentSeries R) :=
  orderTopology R

scoped instance instIsTopologicalRing : IsTopologicalRing (LaurentSeries R) :=
  (orderRingSubgroupsBasis (R := R)).toRingFilterBasis.isTopologicalRing

/-- The `T`-adic topology is Hausdorff. -/
scoped instance instT2Space : T2Space (LaurentSeries R) := by
  apply (AddGroupFilterBasis.t2Space_iff_sInter_subset
    (orderRingSubgroupsBasis (R := R)).toRingFilterBasis.toAddGroupFilterBasis rfl).mpr
  intro f hf
  apply Set.mem_singleton_iff.mpr
  apply HahnSeries.ext
  funext j
  have hmem : f ∈ orderAddSubgroup (j + 1) :=
    (Set.mem_sInter.mp hf
      (orderAddSubgroup (R := R) (j + 1) : Set (LaurentSeries R)) ⟨j + 1, rfl⟩)
  simpa only [HahnSeries.coeff_zero] using
    (mem_orderAddSubgroup_iff_coeff (j + 1) f).mp hmem j (by omega)

end OrderTopology

open scoped LaurentSeries.OrderTopology

/-- The subgroups `orderAddSubgroup m` form a basis of neighborhoods of zero. -/
theorem orderTopology_hasBasis_nhds_zero :
    (𝓝 (0 : LaurentSeries R)).HasBasis (fun _ : ℤ ↦ True)
      (fun m ↦ (orderAddSubgroup (R := R) m : Set (LaurentSeries R))) :=
  (orderRingSubgroupsBasis (R := R)).hasBasis_nhds_zero

/-- The translates `f + orderAddSubgroup m` form a basis of neighborhoods of `f`. -/
theorem orderTopology_hasBasis_nhds (f : LaurentSeries R) :
    (𝓝 f).HasBasis (fun _ : ℤ ↦ True) (fun m ↦ {g | g - f ∈ orderAddSubgroup m}) :=
  (orderRingSubgroupsBasis (R := R)).hasBasis_nhds f

theorem isOpen_orderAddSubgroup (m : ℤ) :
    IsOpen (orderAddSubgroup (R := R) m : Set (LaurentSeries R)) :=
  ((orderRingSubgroupsBasis (R := R)).openAddSubgroup m).isOpen

theorem isClosed_orderAddSubgroup (m : ℤ) :
    IsClosed (orderAddSubgroup (R := R) m : Set (LaurentSeries R)) :=
  (orderAddSubgroup m).isClosed_of_isOpen (isOpen_orderAddSubgroup m)

/-- A family converges to `g` if and only if, for every `m`, its coefficients in all degrees below
`m` are eventually those of `g`. -/
theorem tendsto_orderTopology_iff {ι : Type*} {l : Filter ι}
    {f : ι → LaurentSeries R} {g : LaurentSeries R} :
    Tendsto f l (𝓝 g) ↔ ∀ m : ℤ, ∀ᶠ i in l, ∀ j : ℤ, j < m → (f i).coeff j = g.coeff j := by
  rw [(orderTopology_hasBasis_nhds g).tendsto_right_iff]
  simp only [true_implies, Set.mem_ofPred_eq, mem_orderAddSubgroup_iff_coeff,
    HahnSeries.coeff_sub, sub_eq_zero]

/-! ### Lower bounds on the order -/

/-- The order of `z ∈ R⟦T⟧` as a Laurent series is its order as a power series. -/
theorem _root_.HahnSeries.orderTop_ofPowerSeries {R : Type*} [Semiring R] (z : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R z).orderTop = WithTop.map (fun n : ℕ ↦ (n : ℤ)) z.order := by
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.orderTop_embDomain]
  suffices h : (HahnSeries.toPowerSeries.symm z).orderTop = z.order by rw [h]; rfl
  by_cases hz : z = 0
  · simp only [hz, map_zero, HahnSeries.orderTop_zero, PowerSeries.order_zero]
    rfl
  rw [← PowerSeries.coe_toNat_order hz]
  apply HahnSeries.orderTop_eq_of_le
  · exact PowerSeries.coeff_order hz
  · intro n hn
    have hle := PowerSeries.order_le n (show PowerSeries.coeff n z ≠ 0 from hn)
    rw [← PowerSeries.coe_toNat_order hz] at hle
    exact_mod_cast hle

/-- A power series has no terms of negative degree. -/
theorem ofPowerSeries_mem_orderAddSubgroup_zero (P : PowerSeries R) :
    HahnSeries.ofPowerSeries ℤ R P ∈ orderAddSubgroup 0 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [PowerSeries.coeff_coe, ite_eq_left hj]

/-- A power series without constant term is `O(T)`. -/
theorem ofPowerSeries_mem_orderAddSubgroup_one {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    HahnSeries.ofPowerSeries ℤ R f ∈ orderAddSubgroup 1 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [PowerSeries.coeff_coe]
  by_cases hj0 : j < 0
  · rw [ite_eq_left hj0]
  · obtain rfl : j = 0 := by omega
    simpa only [lt_self_iff_false, ite_false, Int.natAbs_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf

/-- A power series `f` without constant term is `f'(0) T + O(T ^ 2)`. -/
theorem ofPowerSeries_sub_linear_mem_two {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    HahnSeries.ofPowerSeries ℤ R f - HahnSeries.single (1 : ℤ) (f.coeff 1) ∈
      orderAddSubgroup 2 := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [HahnSeries.coeff_sub]
  by_cases hj1 : j = 1
  · subst j
    simp only [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.coeff_single_same, sub_self]
  · rw [(mem_orderAddSubgroup_iff_coeff 1 _).mp (ofPowerSeries_mem_orderAddSubgroup_one hf) j
      (by omega), HahnSeries.coeff_single_of_ne hj1, sub_self]

/-- A Laurent series `f = O(1)` is the power series `∑ₙ f_n Tⁿ`. -/
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

/-- A series `b T ^ m + O(T ^ (m + 1))` is `O(T ^ m)`. -/
theorem mem_orderAddSubgroup_of_sub_single_mem {f : LaurentSeries R} {m : ℤ} {b : R}
    (hf : f - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) : f ∈ orderAddSubgroup m := by
  simpa only [sub_add_cancel] using
    add_mem (orderAddSubgroup_antitone (show m ≤ m + 1 by omega) hf)
      (show HahnSeries.single m b ∈ orderAddSubgroup m from HahnSeries.orderTop_single_le)

/-- If `f = O(T ^ m)`, then `f - f_m T ^ m = O(T ^ (m + 1))`. -/
theorem sub_single_coeff_mem_orderAddSubgroup {f : LaurentSeries R} {m : ℤ}
    (hf : f ∈ orderAddSubgroup m) :
    f - HahnSeries.single m (f.coeff m) ∈ orderAddSubgroup (m + 1) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [HahnSeries.coeff_sub]
  by_cases hjm : j = m
  · subst j
    rw [HahnSeries.coeff_single_same, sub_self]
  · rw [(mem_orderAddSubgroup_iff_coeff m f).mp hf j (by omega),
      HahnSeries.coeff_single_of_ne hjm, sub_self]

/-- `f - c T ^ v(f)`, where `c` is the coefficient of `f` in degree `v(f)`, is
`O(T ^ (v(f) + 1))`. -/
theorem sub_leadingTerm_mem_orderAddSubgroup (f : LaurentSeries R) :
    f - HahnSeries.single f.order (f.coeff f.order) ∈ orderAddSubgroup (f.order + 1) :=
  sub_single_coeff_mem_orderAddSubgroup (mem_orderAddSubgroup_order f)

/-- A series `b T ^ m + O(T ^ (m + 1))` with `b ≠ 0` has order `m`. -/
theorem order_eq_of_sub_single_mem {f : LaurentSeries R} {m : ℤ} {b : R} (hb : b ≠ 0)
    (hf : f - HahnSeries.single m b ∈ orderAddSubgroup (m + 1)) : f.order = m := by
  have hc := (mem_orderAddSubgroup_iff_coeff (m + 1) _).mp hf m (by omega)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same, sub_eq_zero] at hc
  have hn : f.coeff m ≠ 0 := hc ▸ hb
  have ht : f.orderTop = (m : WithTop ℤ) := le_antisymm
    (HahnSeries.orderTop_le_of_coeff_ne_zero hn) (mem_orderAddSubgroup_of_sub_single_mem hf)
  exact_mod_cast (HahnSeries.order_eq_orderTop_of_ne_zero
    (HahnSeries.ne_zero_of_coeff_ne_zero hn)).trans ht

/-- `f - ∑_{j < a} f_j T ^ j = O(T ^ a)`. -/
theorem sub_truncLT_mem_orderAddSubgroup (G : LaurentSeries R) (a : ℤ) :
    G - HahnSeries.truncLT a G ∈ orderAddSubgroup a := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_truncLT_of_lt hj, sub_self]

/-- The truncation `∑_{j < n} f_j T ^ j` is the finite sum over `v(f) ≤ j < n`. -/
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

/-! ### Truncations and continuous homomorphisms -/

/-- The truncations `∑_{j < n} f_j T ^ j` of `f` converge to `f` as `n → ∞`. -/
theorem tendsto_truncLT_orderTopology (f : LaurentSeries R) :
    Tendsto (fun n : ℕ ↦ HahnSeries.truncLT (n : ℤ) f) atTop (𝓝 f) := by
  apply tendsto_orderTopology_iff.mpr
  intro m
  refine eventually_atTop.mpr ⟨m.toNat, ?_⟩
  intro n hn j hj
  apply HahnSeries.coeff_truncLT_of_lt
  omega

section Uniqueness

variable {A : Type*} [CommRing A]

private theorem ringHom_single_eq_of_C_X_eq (F H : LaurentSeries R →+* A)
    (hC : ∀ b : R, F (HahnSeries.C b) = H (HahnSeries.C b))
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) = H (HahnSeries.single (1 : ℤ) (1 : R)))
    (j : ℤ) (b : R) :
    F (HahnSeries.single j b) = H (HahnSeries.single j b) := by
  have hF : F (HahnSeries.single (1 : ℤ) (1 : R)) *
      F (HahnSeries.single (-1 : ℤ) (1 : R)) = 1 := by
    rw [← map_mul]
    simp
  have hH : F (HahnSeries.single (1 : ℤ) (1 : R)) *
      H (HahnSeries.single (-1 : ℤ) (1 : R)) = 1 := by
    rw [hX, ← map_mul]
    simp
  have hneg := inv_unique hF hH
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
  have hs : (HahnSeries.single j b : LaurentSeries R) =
      HahnSeries.C b * HahnSeries.single j 1 := by
    simp only [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hs, map_mul, map_mul, hC, hone]

variable [TopologicalSpace A] [T2Space A]

/-- Two continuous ring homomorphisms from `R((T))` to a Hausdorff ring that agree on the
constants and at `T` are equal. -/
theorem continuous_ringHom_ext (F H : LaurentSeries R →+* A) (hF : Continuous F)
    (hH : Continuous H) (hC : ∀ b : R, F (HahnSeries.C b) = H (HahnSeries.C b))
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) = H (HahnSeries.single (1 : ℤ) (1 : R))) :
    F = H := by
  apply RingHom.ext
  intro f
  apply tendsto_nhds_unique_of_forall
    ((hF.tendsto f).comp (tendsto_truncLT_orderTopology f))
    ((hH.tendsto f).comp (tendsto_truncLT_orderTopology f))
  intro n
  simp only [Function.comp_def, truncLT_eq_sum_Ico, map_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ ringHom_single_eq_of_C_X_eq F H hC hX j (f.coeff j))

/-- Two continuous `R`-algebra homomorphisms from `R((T))` to a Hausdorff `R`-algebra that agree
at `T` are equal. -/
theorem continuous_algHom_ext_X [Algebra R A] (F H : LaurentSeries R →ₐ[R] A) (hF : Continuous F)
    (hH : Continuous H)
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) = H (HahnSeries.single (1 : ℤ) (1 : R))) :
    F = H := by
  have hC (b : R) : F (HahnSeries.C b) = H (HahnSeries.C b) := by
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C] using (F.commutes b).trans (H.commutes b).symm
  exact AlgHom.toRingHom_injective
    (continuous_ringHom_ext F.toRingHom H.toRingHom hF hH hC hX)

end Uniqueness

/-! ### Continuity of the derivative -/

/-- If `f = O(T ^ m)`, then `f' = O(T ^ (m - 1))`. -/
theorem derivative_mem_orderAddSubgroup (m : ℤ) (f : LaurentSeries R)
    (hf : f ∈ orderAddSubgroup m) : derivative R f ∈ orderAddSubgroup (m - 1) := by
  rw [mem_orderAddSubgroup_iff_coeff]
  intro j hj
  rw [coeff_derivative, (mem_orderAddSubgroup_iff_coeff m f).mp hf (j + 1) (by omega), mul_zero]

/-- The derivative `d / dT` is continuous for the `T`-adic topology. -/
theorem continuous_derivative : Continuous (derivative R : LaurentSeries R → LaurentSeries R) := by
  refine continuous_iff_continuousAt.mpr fun f ↦ ?_
  refine ((orderTopology_hasBasis_nhds f).tendsto_iff
    (orderTopology_hasBasis_nhds (derivative R f))).mpr fun m _ ↦ ⟨m + 1, trivial, fun g hg ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rw [← map_sub]
  simpa only [add_sub_cancel_right] using derivative_mem_orderAddSubgroup (m + 1) (g - f) hg

/-! ### Power series -/

section PowerSeries

open scoped PowerSeries.WithPiTopology

/-- Over a discrete ring `R`, the inclusion `R⟦T⟧ → R((T))` is continuous for the topology of
coefficientwise convergence on `R⟦T⟧`. -/
theorem continuous_ofPowerSeries [TopologicalSpace R] [DiscreteTopology R] :
    Continuous (HahnSeries.ofPowerSeries ℤ R) := by
  refine continuous_iff_continuousAt.mpr fun g ↦ tendsto_orderTopology_iff.mpr fun m ↦ ?_
  have hcoeff (n : ℕ) : ∀ᶠ f in 𝓝 g, PowerSeries.coeff n f = PowerSeries.coeff n g := by
    simpa only [nhds_discrete, tendsto_pure] using
      (PowerSeries.WithPiTopology.continuous_coeff R n).tendsto g
  filter_upwards [(Set.finite_Iio m.toNat).eventually_all.mpr fun n _ ↦ hcoeff n] with f hf j hj
  by_cases hjneg : j < 0
  · simp only [PowerSeries.coeff_coe, ite_eq_left hjneg]
  · lift j to ℕ using le_of_not_gt hjneg
    simpa only [HahnSeries.ofPowerSeries_apply_coeff] using hf j (by simp only [Set.mem_Iio]; omega)

end PowerSeries

end

/-! ### Comparison with the valued topology over a field -/

open WithZero in
/-- Over a field `K`, the `T`-adic topology on `K((T))` is the topology of the `T`-adic valuation
of `K((T))`. -/
theorem orderTopology_eq_valued (K : Type*) [Field K] :
    orderTopology K =
      (Valued.toUniformSpace (R := LaurentSeries K) (Γ₀ := ℤᵐ⁰)).toTopologicalSpace := by
  have hle (m : ℤ) (x : LaurentSeries K) :
      Valued.v x ≤ exp (-m) ↔ x ∈ orderAddSubgroup m := by
    rw [valuation_le_iff_coeff_lt_eq_zero, mem_orderAddSubgroup_iff_coeff]
  refine IsTopologicalAddGroup.ext
    (orderRingSubgroupsBasis (R := K)).toRingFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
    inferInstance ?_
  refine (orderRingSubgroupsBasis (R := K)).hasBasis_nhds_zero.ext
    (Valued.hasBasis_nhds_zero _ _) (fun m _ ↦ ?_) (fun γ _ ↦ ?_)
  · have h0 : Valued.v.restrict (HahnSeries.single m (1 : K) : LaurentSeries K) ≠ 0 := by
      simp
    refine ⟨Units.mk0 _ h0, trivial, fun x hx ↦ ?_⟩
    rw [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff,
      valuation_single_zpow] at hx
    exact (hle m x).mp hx.le
  · have hr : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
    refine ⟨1 - log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1), trivial, fun x hx ↦ ?_⟩
    rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact ((hle _ x).mpr hx).trans_lt ((exp_lt_exp.mpr (by omega)).trans_eq (exp_log hr))

end LaurentSeries
