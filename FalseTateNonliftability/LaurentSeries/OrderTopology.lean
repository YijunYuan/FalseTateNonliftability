module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# The Laurent order topology over a commutative coefficient ring

The subgroups of series vanishing in every degree below an integer define
a Hausdorff ring topology, including over rings with nilpotents. The topology
is named explicitly and is never installed as a global instance.

Convergence means eventual agreement of all lower coefficients simultaneously,
rather than separate convergence in each fixed degree.

This is blueprint lemma `nl:laurent-order-topology`.
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

/-- The order subgroups impose simultaneous vanishing in all lower degrees. -/
theorem mem_orderAddSubgroup_iff_coeff (m : ℤ) (f : LaurentSeries R) :
    f ∈ orderAddSubgroup m ↔ ∀ j : ℤ, j < m → f.coeff j = 0 := by
  simpa only [mem_orderAddSubgroup, WithTop.coe_lt_coe] using
    (HahnSeries.le_orderTop_iff_forall (x := f) (i := (m : WithTop ℤ)))

theorem orderAddSubgroup_antitone : Antitone (orderAddSubgroup (R := R)) := by
  intro m n hmn f hf
  exact (WithTop.coe_le_coe.mpr hmn).trans hf

/-- The lower-order bound for a product remains valid with zero divisors. -/
theorem mul_mem_orderAddSubgroup {m n : ℤ} {f g : LaurentSeries R}
    (hf : f ∈ orderAddSubgroup m) (hg : g ∈ orderAddSubgroup n) :
    f * g ∈ orderAddSubgroup (m + n) := by
  change ((m + n : ℤ) : WithTop ℤ) ≤ (f * g).orderTop
  calc
    _ = (m : WithTop ℤ) + (n : WithTop ℤ) := WithTop.coe_add _ _
    _ ≤ f.orderTop + g.orderTop := add_le_add hf hg
    _ ≤ _ := HahnSeries.orderTop_add_le_mul

/-- The convention `order 0 = 0` still provides a valid lower bound. -/
theorem mem_orderAddSubgroup_order (f : LaurentSeries R) :
    f ∈ orderAddSubgroup f.order := by
  by_cases hf : f = 0
  · simp [hf]
  · change (f.order : WithTop ℤ) ≤ f.orderTop
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hf).le

/-- The actual order subgroups satisfy the canonical ring-basis axioms. -/
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

/-- The ring topology defined by Laurent order bounds. This named topology
does not override existing valued-field topology instances. -/
@[instance_reducible]
def orderTopology (R : Type*) [CommRing R] : TopologicalSpace (LaurentSeries R) :=
  (orderRingSubgroupsBasis (R := R)).topology

theorem orderTopology_isTopologicalRing :
    @IsTopologicalRing (LaurentSeries R) (orderTopology R) _ :=
  (orderRingSubgroupsBasis (R := R)).toRingFilterBasis.isTopologicalRing

theorem orderTopology_isTopologicalAddGroup :
    @IsTopologicalAddGroup (LaurentSeries R) (orderTopology R) _ :=
  (orderRingSubgroupsBasis (R := R)).toRingFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup

/-- The specified order subgroups are a neighborhood basis of zero. -/
theorem orderTopology_hasBasis_nhds_zero :
    HasBasis (@nhds (LaurentSeries R) (orderTopology R) 0)
      (fun _ : ℤ ↦ True) (fun m ↦ (orderAddSubgroup (R := R) m : Set (LaurentSeries R))) :=
  (orderRingSubgroupsBasis (R := R)).hasBasis_nhds_zero

/-- The translated order subgroups form the neighborhood basis at every series. -/
theorem orderTopology_hasBasis_nhds (f : LaurentSeries R) :
    HasBasis (@nhds (LaurentSeries R) (orderTopology R) f)
      (fun _ : ℤ ↦ True) (fun m ↦ {g | g - f ∈ orderAddSubgroup m}) :=
  (orderRingSubgroupsBasis (R := R)).hasBasis_nhds f

theorem isOpen_orderAddSubgroup (m : ℤ) :
    @IsOpen (LaurentSeries R) (orderTopology R) (orderAddSubgroup (R := R) m) := by
  let := orderTopology R
  exact ((orderRingSubgroupsBasis (R := R)).openAddSubgroup m).isOpen

/-- A nonzero coefficient separates a series from zero in the order topology. -/
theorem orderTopology_t2Space : @T2Space (LaurentSeries R) (orderTopology R) := by
  let := orderTopology R
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

/-- Convergence requires eventual simultaneous agreement in every degree
below each prescribed bound, with the degree quantifier inside the eventuality. -/
theorem tendsto_orderTopology_iff {ι : Type*} {l : Filter ι}
    {f : ι → LaurentSeries R} {g : LaurentSeries R} :
    Tendsto f l (@nhds (LaurentSeries R) (orderTopology R) g) ↔
      ∀ m : ℤ, ∀ᶠ i in l, ∀ j : ℤ, j < m → (f i).coeff j = g.coeff j := by
  rw [(orderTopology_hasBasis_nhds g).tendsto_right_iff]
  simp only [true_implies, Set.mem_ofPred_eq, mem_orderAddSubgroup_iff_coeff,
    HahnSeries.coeff_sub, sub_eq_zero]

end

end LaurentSeries
