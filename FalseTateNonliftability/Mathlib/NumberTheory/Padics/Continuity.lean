/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod

/-!
# Continuity of the reduction `ℤ_p → ℤ/pℤ` and division by `p`

Let `p` be a prime number. The reduction `ℤ_p → ℤ/pℤ` is locally constant, hence continuous for
the discrete topology on `ℤ/pℤ`. Multiplication by `p` is a closed embedding of `ℤ_p` into itself.
Consequently, if a sequence `(p x_n)` converges in `ℤ_p` to `b`, then `b = p c` for some `c ∈ ℤ_p`
and `x_n → c`.

This file is a candidate for upstreaming to Mathlib (`Mathlib.NumberTheory.Padics.RingHoms`).

## Main results

* `PadicInt.continuous_toZMod`: the reduction `ℤ_p → ℤ/pℤ` is continuous.
* `PadicInt.exists_tendsto_of_prime_mul_tendsto`: if `p x_n → b` in `ℤ_p`, then `x_n → c` for some
  `c` with `p c = b`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.2 (`p`-adic powers of principal units) and the proof of Proposition 4.3 (the limit of
  `(q + d_n) / p` in `ℤ_p`).
-/

@[expose] public section

open Filter Topology

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The reduction `ℤ_p → ℤ/pℤ` is continuous. -/
theorem continuous_toZMod : Continuous (toZMod : ℤ_[p] → ZMod p) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have heq : ∀ᶠ y in 𝓝 x, toZMod y = toZMod x := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    apply sub_eq_zero.mp
    rw [← map_sub, ← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
    exact (norm_lt_one_iff_dvd _).mp (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  apply tendsto_const_nhds.congr'
  filter_upwards [heq] with y hy
  exact hy.symm

/-- If `(p x_n)` converges to `b` in `ℤ_p`, then `(x_n)` converges to some `c ∈ ℤ_p` with
`p c = b`. -/
theorem exists_tendsto_of_prime_mul_tendsto {x : ℕ → ℤ_[p]} {b : ℤ_[p]}
    (h : Tendsto (fun n ↦ (p : ℤ_[p]) * x n) atTop (𝓝 b)) :
    ∃ c : ℤ_[p], (p : ℤ_[p]) * c = b ∧ Tendsto x atTop (𝓝 c) := by
  have hp : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have he : IsClosedEmbedding fun z : ℤ_[p] ↦ (p : ℤ_[p]) * z :=
    (continuous_const.mul continuous_id).isClosedEmbedding fun _ _ h ↦ mul_left_cancel₀ hp h
  obtain ⟨c, hc⟩ := he.isClosed_range.mem_of_tendsto h (Eventually.of_forall fun n ↦ ⟨x n, rfl⟩)
  refine ⟨c, hc, he.tendsto_nhds_iff.mpr ?_⟩
  simpa only [Function.comp_def, hc] using h

end PadicInt
