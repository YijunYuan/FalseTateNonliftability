/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.CoefficientRing.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The coefficient ring `A` is a discrete valuation ring

Let `O` be a discrete valuation ring with residue field `κ`. The coefficient ring `A`, the
`𝔪`-adic completion of `O((T))`, is a discrete valuation ring, and every uniformizer `ϖ` of `O`
is a uniformizer of `A`. Together with `CoefficientRing.isAdicComplete` and
`CoefficientRing.residueFieldEquiv` this is the statement of Yuan, Definition 1.1, that `A` is a
complete discrete valuation ring with uniformizer `ϖ` and residue field `κ((T))`; the proofs of the
main results do not use it.

## Main results

* `CoefficientRing.isDomain`, `CoefficientRing.isDiscreteValuationRing`: `A` is a discrete
  valuation ring.
* `CoefficientRing.irreducible_algebraMap`: a uniformizer of `O` is a uniformizer of `A`.

## References

* Yuan, Definition 1.1.
-/

@[expose] public section

noncomputable section

namespace FalseTateNonliftability.CoefficientRing

open IsLocalRing (maximalIdeal)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem maximalIdeal_eq_span {ϖ : O} (hϖ : Irreducible ϖ) :
    maximalIdeal (CoefficientRing O) = Ideal.span {algebraMap O (CoefficientRing O) ϖ} := by
  rw [maximalIdeal_eq_map, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

private theorem algebraMap_pow_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    algebraMap O (CoefficientRing O) ϖ ^ n ≠ 0 := by
  intro h
  have h' := congrArg (reduction O n) h
  rw [← map_pow, reduction_algebraMap, map_zero, ← map_zero HahnSeries.C] at h'
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp (HahnSeries.C_injective h')
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at hmem
  omega

private theorem exists_eq_pow_mul_unit {ϖ : O} (hϖ : Irreducible ϖ) {x : CoefficientRing O}
    (hx : x ≠ 0) : ∃ (n : ℕ) (u : (CoefficientRing O)ˣ),
      x = algebraMap O (CoefficientRing O) ϖ ^ n * u := by
  set t := algebraMap O (CoefficientRing O) ϖ
  have hmax := maximalIdeal_eq_span hϖ
  obtain ⟨n, hn, hn1⟩ : ∃ n, x ∈ Ideal.span {t ^ n} ∧ x ∉ Ideal.span {t ^ (n + 1)} := by
    by_contra! h
    have hmem (n : ℕ) : x ∈ Ideal.span {t ^ n} := by
      induction n with
      | zero => simp
      | succ n ih => exact h n ih
    refine hx (IsHausdorff.haus (I := maximalIdeal (CoefficientRing O)) inferInstance x
      fun n ↦ ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hmax, Ideal.span_singleton_pow]
    exact hmem n
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hn
  have hy : IsUnit y := by
    by_contra hy
    have hyt : y ∈ Ideal.span {t} := hmax ▸ (IsLocalRing.mem_maximalIdeal y).mpr hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hyt
    exact hn1 (Ideal.mem_span_singleton.mpr ⟨z, by ring⟩)
  exact ⟨n, hy.unit, rfl⟩

instance isDomain : IsDomain (CoefficientRing O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : NoZeroDivisors (CoefficientRing O) := ⟨fun {a b} hab ↦ by
    by_contra! h
    obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit hϖ h.1
    obtain ⟨m, v, rfl⟩ := exists_eq_pow_mul_unit hϖ h.2
    have h' : algebraMap O (CoefficientRing O) ϖ ^ (n + m) * ↑(u * v) = 0 := by
      rw [← hab, pow_add, Units.val_mul]
      ring
    exact algebraMap_pow_ne_zero hϖ (n + m) ((u * v).isUnit.mul_left_eq_zero.mp h')⟩
  exact NoZeroDivisors.to_isDomain _

/-- A uniformizer of `O` is a uniformizer of `A`. -/
theorem irreducible_algebraMap {ϖ : O} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap O (CoefficientRing O) ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using algebraMap_pow_ne_zero hϖ 1) (maximalIdeal_eq_span hϖ)

instance isDiscreteValuationRing : IsDiscreteValuationRing (CoefficientRing O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine .ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap O (CoefficientRing O) ϖ, irreducible_algebraMap hϖ, fun hx ↦ ?_⟩
  obtain ⟨n, u, rfl⟩ := exists_eq_pow_mul_unit hϖ hx
  exact ⟨n, u, rfl⟩

end FalseTateNonliftability.CoefficientRing
