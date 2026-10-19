module

public import FalseTateNonliftability.CoefficientRing.LocalRing

/-!
# Discrete valuation on the actual completed coefficient ring

Finite coefficient quotients show that no power of the original uniformizer
vanishes in the canonical principal completion. Adic separatedness and the
proved local structure then give a unit-times-power factorization of every
nonzero element. This proves that the same completion is a discrete valuation
ring, without assuming that it is a domain.

This implements `nl:completed-coefficient-dvr`.
-/

@[expose] public section

noncomputable section

namespace LaurentSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (π : O) (hπ : Irreducible π)

include hπ

omit [IsDiscreteValuationRing O] in
/-- The actual finite quotient at level `n + 1` detects the `n`-th power
of the original constant uniformizer. No domain property of the completion
is assumed. -/
theorem completedUniformizer_pow_ne_zero (n : ℕ) :
    (algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)) ^ n ≠ 0 := by
  intro h
  have heq : (algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)) ^ n =
      algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C (π ^ n)) := by
    rw [← map_pow, ← map_pow]
  rw [heq] at h
  have hz := congrArg (fun x : PrincipalCompletion π ↦
    (completedPrincipalReduction π (n + 1) x).coeff 0) h
  rw [completedPrincipalReduction_algebraMap_coeff] at hz
  have hd : π ^ (n + 1) ∣ π ^ n := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa using hz
  have := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp hd
  omega

/-- Adic separatedness bounds the powers of the actual uniformizer that
can divide a given nonzero element of the canonical completion. -/
theorem exists_not_mem_completedUniformizer_pow
    {x : PrincipalCompletion π} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∉ Ideal.span
      {((algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)) ^ n)} := by
  let := principalCompletion_isLocalRing π hπ
  let := principalCompletion_isAdicComplete π hπ
  by_contra! h
  apply hx
  apply IsHausdorff.haus
    (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal (PrincipalCompletion π))
      (PrincipalCompletion π)) x
  intro n
  apply SModEq.zero.mpr
  simpa only [smul_eq_mul, Ideal.mul_top, principalCompletion_maximalIdeal π hπ,
    Ideal.span_singleton_pow] using h n

/-- Every nonzero element of the actual completion is a power of the original
uniformizer times an actual unit, obtained from separatedness and locality. -/
theorem exists_completedUniformizer_pow_mul_unit
    {x : PrincipalCompletion π} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (PrincipalCompletion π)ˣ),
      x = (algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)) ^ n * u := by
  classical
  let := principalCompletion_isLocalRing π hπ
  let t := algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)
  have hn : ∃ n : ℕ, x ∉ Ideal.span ({t ^ n} : Set (PrincipalCompletion π)) :=
    exists_not_mem_completedUniformizer_pow π hπ hx
  have hn0 : Nat.find hn ≠ 0 := by
    intro hzero
    have h := Nat.find_spec hn
    rw [hzero] at h
    simp at h
  obtain ⟨n, heq⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hxmem : x ∈ Ideal.span ({t ^ n} : Set (PrincipalCompletion π)) := by
    by_contra h
    have hle := Nat.find_min' hn h
    omega
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxmem
  have hyunit : IsUnit y := by
    by_contra hunit
    have hymem : y ∈ IsLocalRing.maximalIdeal (PrincipalCompletion π) := hunit
    rw [principalCompletion_maximalIdeal π hπ] at hymem
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hymem
    apply Nat.find_spec hn
    rw [heq]
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    change x = t ^ (n + 1) * z
    rw [hy, hz, pow_succ, mul_assoc]
  obtain ⟨u, hu⟩ := hyunit
  refine ⟨n, u, ?_⟩
  simpa only [hu] using hy

/-- Domain structure is a consequence of the constructed unit-power
factorizations and finite-quotient nonvanishing. -/
theorem principalCompletion_isDomain : IsDomain (PrincipalCompletion π) := by
  let t := algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)
  let : Nontrivial (PrincipalCompletion π) :=
    ⟨⟨t ^ 0, 0, completedUniformizer_pow_ne_zero π hπ 0⟩⟩
  let : NoZeroDivisors (PrincipalCompletion π) := ⟨by
    intro a b hab
    by_contra! h
    obtain ⟨n, u, ha⟩ := exists_completedUniformizer_pow_mul_unit π hπ h.1
    obtain ⟨m, v, hb⟩ := exists_completedUniformizer_pow_mul_unit π hπ h.2
    have ht : t ^ (n + m) * (↑(u * v) : PrincipalCompletion π) = 0 := by
      calc
        _ = a * b := by rw [ha, hb, pow_add, Units.val_mul]; ring
        _ = 0 := hab
    have hz := congrArg (fun x : PrincipalCompletion π ↦ x * ↑((u * v)⁻¹)) ht
    have hzero : t ^ (n + m) = 0 := by simpa [mul_assoc] using hz
    exact completedUniformizer_pow_ne_zero π hπ (n + m) hzero⟩
  exact NoZeroDivisors.to_isDomain _

/-- The same unit-power factorizations make every actual ideal principal. -/
theorem principalCompletion_isPrincipalIdealRing :
    IsPrincipalIdealRing (PrincipalCompletion π) := by
  classical
  let t := algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)
  refine ⟨fun H ↦ ?_⟩
  by_cases hH : H = ⊥
  · subst H
    infer_instance
  have hx : ∃ x ∈ H, x ≠ 0 := by
    by_contra! h
    apply hH
    apply bot_unique
    intro x hx
    change x = 0
    exact h x hx
  obtain ⟨x, hx, hx0⟩ := hx
  have hn : ∃ n : ℕ, ∃ u : (PrincipalCompletion π)ˣ,
      t ^ n * (u : PrincipalCompletion π) ∈ H := by
    obtain ⟨n, u, hu⟩ := exists_completedUniformizer_pow_mul_unit π hπ hx0
    exact ⟨n, u, hu ▸ hx⟩
  obtain ⟨u, hu⟩ := Nat.find_spec hn
  have htn : t ^ Nat.find hn ∈ H := by
    have h := H.mul_mem_right (↑u⁻¹) hu
    simpa [mul_assoc] using h
  refine ⟨⟨t ^ Nat.find hn, ?_⟩⟩
  apply le_antisymm
  · intro y hy
    by_cases hy0 : y = 0
    · simp [hy0]
    obtain ⟨m, v, hv⟩ := exists_completedUniformizer_pow_mul_unit π hπ hy0
    have hm : ∃ u : (PrincipalCompletion π)ˣ, t ^ m * (u : PrincipalCompletion π) ∈ H :=
      ⟨v, hv ▸ hy⟩
    have hnm := Nat.find_min' hn hm
    apply Ideal.mem_span_singleton.mpr
    rw [hv]
    exact dvd_mul_of_dvd_left (pow_dvd_pow t hnm) _
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact htn

/-- The canonical completed Laurent coefficient ring is a genuine DVR. -/
theorem principalCompletion_isDiscreteValuationRing :
    letI := principalCompletion_isDomain π hπ
    IsDiscreteValuationRing (PrincipalCompletion π) := by
  let := principalCompletion_isDomain π hπ
  let := principalCompletion_isLocalRing π hπ
  let := principalCompletion_isPrincipalIdealRing π hπ
  refine { not_a_field' := ?_ }
  intro hzero
  have ht : algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π) ∈
      IsLocalRing.maximalIdeal (PrincipalCompletion π) := by
    rw [principalCompletion_maximalIdeal π hπ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have ht0 : algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π) = 0 := by
    simpa only [hzero, Submodule.mem_bot] using ht
  exact completedUniformizer_pow_ne_zero π hπ 1 (by simpa only [pow_one] using ht0)

/-- The original constant uniformizer is an actual uniformizer of the same DVR. -/
theorem completedUniformizer_irreducible :
    letI := principalCompletion_isDomain π hπ
    Irreducible (algebraMap (LaurentSeries O) (PrincipalCompletion π) (HahnSeries.C π)) := by
  let := principalCompletion_isDomain π hπ
  let := principalCompletion_isLocalRing π hπ
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · simpa only [pow_one] using completedUniformizer_pow_ne_zero π hπ 1
  · exact principalCompletion_maximalIdeal π hπ

end LaurentSeries
