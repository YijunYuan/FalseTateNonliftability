/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.PowerSeries.PrincipalUnitPowers
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Topology.Sequences

/-!
# Compactness of the units of `κ⟦T⟧` and limits of normalized Laurent series

Let `κ` be a finite field with the discrete topology. The units of `κ⟦T⟧` form a compact subset
for the `T`-adic topology, so every sequence of units has a subsequence converging to a unit.
Applied to `T ^ (-v_T(x n)) x n` for nonzero Laurent series `x n`, this gives the convergent
normalized units used in the proof of Yuan, Lemma 4.2. Over a field of characteristic `p`, the
expressions `u ^ (a i) (U i ∘ f) - U i` converge to `u ^ c (V ∘ f) - V` when `a i → c` in `ℤ_p` and
`U i → V`.

## Main results

* `PowerSeries.isCompact_setOf_isUnit`: the units of `κ⟦T⟧` form a compact set.
* `PowerSeries.exists_subseq_tendsto_of_isUnit`: a sequence of units of `κ⟦T⟧` has a subsequence
  converging to a unit.
* `LaurentSeries.exists_subseq_powerSeriesPart_tendsto`: for nonzero `x n ∈ κ((T))`, the units
  `T ^ (-v_T(x n)) x n` have a subsequence converging to a unit of `κ⟦T⟧`.
* `PowerSeries.tendsto_principalUnitPow_mul_subst_sub_of_intCast_tendsto`: continuity of
  `(c, U) ↦ u ^ c (U ∘ f) - U` along integer approximations of `c`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.2.
-/

@[expose] public section

noncomputable section

open scoped Topology PowerSeries.WithPiTopology

namespace PowerSeries

variable {κ : Type*} [Field κ] [TopologicalSpace κ] [DiscreteTopology κ]

/-- The units of `κ⟦T⟧` form a closed subset for the discrete topology on `κ`. -/
theorem isClosed_setOf_isUnit : IsClosed {U : PowerSeries κ | IsUnit U} := by
  simpa only [Set.preimage_ofPred_eq, isUnit_iff_constantCoeff, isUnit_iff_ne_zero] using
    (isClosed_discrete {a : κ | a ≠ 0}).preimage (WithPiTopology.continuous_constantCoeff κ)

/-- Over a finite field, the units of `κ⟦T⟧` form a compact subset. -/
theorem isCompact_setOf_isUnit [Finite κ] : IsCompact {U : PowerSeries κ | IsUnit U} := by
  let : CompactSpace (PowerSeries κ) := inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → κ))
  exact isClosed_setOf_isUnit.isCompact

/-- Over a finite field, every sequence of units of `κ⟦T⟧` has a subsequence converging to a
unit. -/
theorem exists_subseq_tendsto_of_isUnit [Finite κ] (U : ℕ → PowerSeries κ)
    (hU : ∀ n, IsUnit (U n)) :
    ∃ V : PowerSeries κ, IsUnit V ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (U ∘ φ) Filter.atTop (𝓝 V) := by
  let : FirstCountableTopology (PowerSeries κ) :=
    inferInstanceAs (FirstCountableTopology ((Unit →₀ ℕ) → κ))
  exact isCompact_setOf_isUnit.tendsto_subseq hU

end PowerSeries

namespace LaurentSeries

variable {κ : Type*} [Field κ]

/-- For a nonzero `x ∈ κ((T))`, the power series `T ^ (-v_T(x)) x` is a unit. -/
theorem isUnit_powerSeriesPart {x : LaurentSeries κ} (hx : x ≠ 0) :
    IsUnit x.powerSeriesPart := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa only [powerSeriesPart_coeff, Nat.cast_zero, add_zero] using
    HahnSeries.coeff_order_eq_zero.not.mpr hx

/-- Over a finite discrete field, for nonzero `x n ∈ κ((T))` the units `T ^ (-v_T(x n)) x n` have
a subsequence converging to a unit of `κ⟦T⟧`, both in `κ⟦T⟧` and in `κ((T))`. -/
theorem exists_subseq_powerSeriesPart_tendsto [TopologicalSpace κ] [DiscreteTopology κ]
    [Finite κ] (x : ℕ → LaurentSeries κ) (hx : ∀ n, x n ≠ 0) :
    ∃ U : (PowerSeries κ)ˣ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n ↦ (x (φ n)).powerSeriesPart) Filter.atTop
        (𝓝 (U : PowerSeries κ)) ∧
      Filter.Tendsto
        (fun n ↦ HahnSeries.ofPowerSeries ℤ κ (x (φ n)).powerSeriesPart) Filter.atTop
        (@nhds (LaurentSeries κ) (orderTopology κ) (HahnSeries.ofPowerSeries ℤ κ U)) := by
  obtain ⟨V, ⟨U, hU⟩, φ, hφ, hconv⟩ :=
    PowerSeries.exists_subseq_tendsto_of_isUnit (fun n ↦ (x n).powerSeriesPart)
      (fun n ↦ isUnit_powerSeriesPart (hx n))
  have hconv' : Filter.Tendsto (fun n ↦ (x (φ n)).powerSeriesPart) Filter.atTop
      (𝓝 (U : PowerSeries κ)) := by
    simpa only [hU, Function.comp_def] using hconv
  exact ⟨U, φ, hφ, hconv', PowerSeries.tendsto_ofPowerSeries_orderTopology hconv'⟩

end LaurentSeries

namespace PowerSeries

variable {κ : Type*} [Field κ] [TopologicalSpace κ] [DiscreteTopology κ] {p : ℕ} [Fact p.Prime]
  [CharP κ p]

/-- Let `u` be a principal unit of `κ⟦T⟧` and `f(0) = 0`. If integers `a i` converge to `c` in
`ℤ_p` and `U i → V` in `κ⟦T⟧`, then `u ^ (a i) (U i ∘ f) - U i → u ^ c (V ∘ f) - V`. -/
theorem tendsto_principalUnitPow_mul_subst_sub_of_intCast_tendsto {ι : Type*} {l : Filter ι}
    (u : (PowerSeries κ)ˣ) (hu : constantCoeff (u : PowerSeries κ) = 1) {a : ι → ℤ} {c : ℤ_[p]}
    (ha : Filter.Tendsto (fun i ↦ (a i : ℤ_[p])) l (𝓝 c)) {U : ι → PowerSeries κ}
    {V : PowerSeries κ} (hU : Filter.Tendsto U l (𝓝 V)) {f : PowerSeries κ}
    (hf : constantCoeff f = 0) :
    Filter.Tendsto
      (fun i ↦ ((u ^ a i : (PowerSeries κ)ˣ) : PowerSeries κ) * (U i).subst f - U i) l
      (𝓝 (principalUnitPow (u : PowerSeries κ) c * V.subst f - V)) := by
  simpa only [Function.comp_def] using
    ((tendsto_principalUnitPow_of_intCast_tendsto u hu ha).mul
      (((continuous_subst_of_constantCoeff_zero hf).tendsto V).comp hU)).sub hU

end PowerSeries
