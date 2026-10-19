module

public import FalseTateNonliftability.LaurentSeries.Derivative
public import FalseTateNonliftability.LaurentSeries.PrincipalQuotient

/-!
# Coefficient maps and actual Laurent evaluation

Canonical coefficient maps preserve lower support bounds, are continuous
for the named order topologies, and commute with canonical differentiation.
They also commute with actual nilpotent Laurent evaluation. The latter
identity follows from agreement on finite Laurent monomials and the actual
truncation limits, without identifying scalar structures over different rings.

This proves blueprint lemma `nl:laurent-coefficient-naturality`.
-/

@[expose] public section

namespace LaurentSeries

open Filter
open scoped Topology

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp]
theorem mapRingHom_single (ψ : R →+* S) (j : ℤ) (b : R) :
    mapRingHom ψ (HahnSeries.single j b) = HahnSeries.single j (ψ b) :=
  HahnSeries.map_single ψ.toZeroHom

/-- Mapping coefficients can only increase the canonical extended order. -/
theorem orderTop_le_mapRingHom (ψ : R →+* S) (f : LaurentSeries R) :
    f.orderTop ≤ (mapRingHom ψ f).orderTop := by
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro j hj
  rw [mapRingHom_coeff, HahnSeries.coeff_eq_zero_of_lt_orderTop hj, map_zero]

/-- Injective coefficient maps preserve the actual extended Laurent order. -/
theorem orderTop_mapRingHom_of_injective {S : Type*} [CommRing S]
    (ψ : R →+* S) (hψ : Function.Injective ψ) (f : LaurentSeries R) :
    (mapRingHom ψ f).orderTop = f.orderTop := by
  apply le_antisymm ?_ (orderTop_le_mapRingHom ψ f)
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro j hj
  apply hψ
  rw [map_zero]
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop hj

/-- Every integer lower support bound is preserved by coefficient maps. -/
theorem mapRingHom_mem_orderAddSubgroup (ψ : R →+* S) (m : ℤ)
    (f : LaurentSeries R) (hf : f ∈ orderAddSubgroup m) :
    mapRingHom ψ f ∈ orderAddSubgroup m :=
  hf.trans (orderTop_le_mapRingHom ψ f)

/-- The canonical coefficient map is continuous for the two named order topologies. -/
theorem continuous_mapRingHom (ψ : R →+* S) :
    @Continuous (LaurentSeries R) (LaurentSeries S) (orderTopology R) (orderTopology S)
      (mapRingHom ψ) := by
  let := orderTopology R
  let := orderTopology S
  rw [continuous_iff_continuousAt]
  intro f
  change Tendsto (mapRingHom ψ) (nhds f) (nhds (mapRingHom ψ f))
  rw [(orderTopology_hasBasis_nhds f).tendsto_iff
    (orderTopology_hasBasis_nhds (mapRingHom ψ f))]
  intro m _
  refine ⟨m, trivial, ?_⟩
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg ⊢
  rw [← map_sub]
  exact mapRingHom_mem_orderAddSubgroup ψ m (g - f) hg

/-- Coefficient maps commute with the canonical Laurent derivative. -/
theorem mapRingHom_derivative (ψ : R →+* S) (f : LaurentSeries R) :
    mapRingHom ψ (derivative R f) = derivative S (mapRingHom ψ f) := by
  ext j
  simp only [mapRingHom_coeff, coeff_derivative, map_mul, map_intCast]

private theorem ringHom_single_eq_of_C_X_eq
    (F H : LaurentSeries R →+* LaurentSeries S)
    (hC : ∀ b : R, F (HahnSeries.C b) = H (HahnSeries.C b))
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) =
      H (HahnSeries.single (1 : ℤ) (1 : R))) (j : ℤ) (b : R) :
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

private theorem continuous_ringHom_ext_C_X
    (F H : LaurentSeries R →+* LaurentSeries S)
    (hF : @Continuous (LaurentSeries R) (LaurentSeries S)
      (orderTopology R) (orderTopology S) F)
    (hH : @Continuous (LaurentSeries R) (LaurentSeries S)
      (orderTopology R) (orderTopology S) H)
    (hC : ∀ b : R, F (HahnSeries.C b) = H (HahnSeries.C b))
    (hX : F (HahnSeries.single (1 : ℤ) (1 : R)) =
      H (HahnSeries.single (1 : ℤ) (1 : R))) : F = H := by
  let := orderTopology R
  let := orderTopology S
  have := orderTopology_t2Space (R := S)
  apply RingHom.ext
  intro f
  apply tendsto_nhds_unique_of_forall
    ((hF.tendsto f).comp (tendsto_truncLT_orderTopology f))
    ((hH.tendsto f).comp (tendsto_truncLT_orderTopology f))
  intro n
  simp only [Function.comp_def, truncLT_eq_sum_Ico, map_sum]
  exact Finset.sum_congr rfl (fun j _ ↦ ringHom_single_eq_of_C_X_eq F H hC hX j (f.coeff j))

section Evaluation

variable (ψ : R →+* S)
  (δ : R) (U Y : LaurentSeries R) (r : ℕ) (hr : 1 ≤ r) (hδ : δ ^ r = 0)
  (a c : ℤ) (ha : 0 < a) (hc : 0 ≤ c)
  (hU : (a : WithTop ℤ) ≤ U.orderTop)
  (hY : ((-c : ℤ) : WithTop ℤ) ≤ Y.orderTop) (hUunit : IsUnit U)

local notation "sourceEval" => nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
local notation "targetEval" => nilpotentLaurentEval (ψ δ) (mapRingHom ψ U) (mapRingHom ψ Y)
  r hr (Eq.trans (Eq.symm (map_pow ψ δ r)) (Eq.trans (congrArg ψ hδ) (map_zero ψ))) a c ha hc
  (le_trans hU (orderTop_le_mapRingHom ψ U)) (le_trans hY (orderTop_le_mapRingHom ψ Y))
  (IsUnit.map (mapRingHom ψ) hUunit)

/-- Actual Laurent evaluation commutes with every coefficient ring homomorphism.
The nilpotence exponent, both support bounds, and invertibility are transported
from the original data; no injectivity or nontriviality is required. -/
theorem mapRingHom_nilpotentLaurentEval (f : LaurentSeries R) :
    mapRingHom ψ (sourceEval f) = targetEval (mapRingHom ψ f) := by
  let := orderTopology R
  let := orderTopology S
  have hsource := continuous_nilpotentLaurentEval δ U Y r hr hδ a c ha hc hU hY hUunit
  have htarget : Continuous targetEval := continuous_nilpotentLaurentEval _ _ _ _ _ _ _ _ _ _ _ _ _
  have heq : (mapRingHom ψ).comp (sourceEval).toRingHom =
      (targetEval).toRingHom.comp (mapRingHom ψ) := by
    apply continuous_ringHom_ext_C_X
      ((mapRingHom ψ).comp (sourceEval).toRingHom)
      ((targetEval).toRingHom.comp (mapRingHom ψ))
      ((continuous_mapRingHom ψ).comp hsource) (htarget.comp (continuous_mapRingHom ψ))
    · intro b
      change mapRingHom ψ (sourceEval (HahnSeries.C b)) = targetEval (mapRingHom ψ (HahnSeries.C b))
      simp only [nilpotentLaurentEval_C, mapRingHom_C]
    · change mapRingHom ψ (sourceEval (HahnSeries.single (1 : ℤ) (1 : R))) =
        targetEval (mapRingHom ψ (HahnSeries.single (1 : ℤ) (1 : R)))
      simp only [nilpotentLaurentEval_X, mapRingHom_single, map_one, map_add,
        map_mul, mapRingHom_C]
  exact RingHom.congr_fun heq f

end Evaluation

end

end LaurentSeries
