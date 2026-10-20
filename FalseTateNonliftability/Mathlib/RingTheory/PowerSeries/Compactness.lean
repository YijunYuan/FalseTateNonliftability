/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Sequences

/-!
# Compactness of the units of power series over a finite field

Let `κ` be a field with the discrete topology, and equip `κ⟦T⟧` with the topology of
coefficientwise convergence (`PowerSeries.WithPiTopology`), which is the `T`-adic topology. The
units of `κ⟦T⟧`, the series with nonzero constant coefficient, form a closed subset. If `κ` is
finite, then `κ⟦T⟧` is compact, so its units form a compact subset and every sequence of units of
`κ⟦T⟧` has a subsequence converging to a unit.

This file is a candidate for upstreaming to Mathlib (`Mathlib.RingTheory.PowerSeries.PiTopology`).

## Main results

* `PowerSeries.isClosed_setOf_isUnit`: the units of `κ⟦T⟧` form a closed set.
* `PowerSeries.isCompact_setOf_isUnit`: over a finite field, the units of `κ⟦T⟧` form a compact
  set.
* `PowerSeries.exists_subseq_tendsto_of_isUnit`: over a finite field, a sequence of units of
  `κ⟦T⟧` has a subsequence converging to a unit.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  proof of Lemma 4.2 (compactness of `1 + T 𝔽_p⟦T⟧`).
-/

@[expose] public section

open scoped Topology PowerSeries.WithPiTopology

namespace PowerSeries

variable {κ : Type*} [Field κ] [TopologicalSpace κ] [DiscreteTopology κ]

/-- For the discrete topology on the field `κ`, the units of `κ⟦T⟧` form a closed subset. -/
theorem isClosed_setOf_isUnit : IsClosed {U : PowerSeries κ | IsUnit U} := by
  simpa only [Set.preimage_ofPred_eq, isUnit_iff_constantCoeff, isUnit_iff_ne_zero] using
    (isClosed_discrete {a : κ | a ≠ 0}).preimage (WithPiTopology.continuous_constantCoeff κ)

/-- Over a finite discrete field `κ`, the units of `κ⟦T⟧` form a compact subset. -/
theorem isCompact_setOf_isUnit [Finite κ] : IsCompact {U : PowerSeries κ | IsUnit U} := by
  let : CompactSpace (PowerSeries κ) := inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → κ))
  exact isClosed_setOf_isUnit.isCompact

/-- Over a finite discrete field `κ`, every sequence of units of `κ⟦T⟧` has a subsequence
converging to a unit. -/
theorem exists_subseq_tendsto_of_isUnit [Finite κ] (U : ℕ → PowerSeries κ)
    (hU : ∀ n, IsUnit (U n)) :
    ∃ V : PowerSeries κ, IsUnit V ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (U ∘ φ) Filter.atTop (𝓝 V) := by
  let : FirstCountableTopology (PowerSeries κ) :=
    inferInstanceAs (FirstCountableTopology ((Unit →₀ ℕ) → κ))
  exact isCompact_setOf_isUnit.tendsto_subseq hU

end PowerSeries
