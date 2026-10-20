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
# Compactness of power-series units and actual Laurent normalization

Over a finite discrete coefficient field, the original power-series unit
subset is compact. This supplies the convergent normalized units used in
Yuan, Lemma 4.1, without changing the power-series or Laurent-series carriers.
-/

@[expose] public section

noncomputable section

open scoped Topology PowerSeries.WithPiTopology

namespace PowerSeries

variable {k : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]

/-- The original unit subset is closed over a discrete coefficient field. -/
theorem isClosed_setOf_isUnit : IsClosed {U : PowerSeries k | IsUnit U} := by
  simpa only [Set.preimage_ofPred_eq, isUnit_iff_constantCoeff, isUnit_iff_ne_zero] using
    (isClosed_discrete {a : k | a ≠ 0}).preimage
      (WithPiTopology.continuous_constantCoeff k)

/-- Over a finite field, the actual power-series units form a compact subset
of the countable coefficient product. -/
theorem isCompact_setOf_isUnit [Finite k] : IsCompact {U : PowerSeries k | IsUnit U} := by
  let : CompactSpace (PowerSeries k) :=
    inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → k))
  exact isClosed_setOf_isUnit.isCompact

/-- Any sequence of original power-series units has a subsequence whose
power-series limit is again a unit. -/
theorem exists_subseq_tendsto_of_isUnit [Finite k]
    (U : ℕ → PowerSeries k) (hU : ∀ n, IsUnit (U n)) :
    ∃ V : PowerSeries k, IsUnit V ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (U ∘ φ) Filter.atTop (nhds V) := by
  let : FirstCountableTopology (PowerSeries k) :=
    inferInstanceAs (FirstCountableTopology ((Unit →₀ ℕ) → k))
  exact isCompact_setOf_isUnit.tendsto_subseq hU

/-- The subsequential limit can be taken in the actual power-series unit
group, while convergence is measured on its original series values. -/
theorem exists_subseq_tendsto_units_val [Finite k]
    (U : ℕ → (PowerSeries k)ˣ) :
    ∃ V : (PowerSeries k)ˣ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => (U (φ n) : PowerSeries k)) Filter.atTop
        (nhds (V : PowerSeries k)) := by
  obtain ⟨V, ⟨v, hv⟩, φ, hφ, hconv⟩ :=
    exists_subseq_tendsto_of_isUnit (fun n => (U n : PowerSeries k)) (fun n => (U n).isUnit)
  exact ⟨v, φ, hφ, by simpa only [hv, Function.comp_def] using hconv⟩

/-- The same subsequence converges on the actual Laurent carrier in the
named order topology; the nonnegative support bound is retained. -/
theorem exists_subseq_tendsto_units_val_orderTopology [Finite k]
    (U : ℕ → (PowerSeries k)ˣ) :
    ∃ V : (PowerSeries k)ˣ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => (U (φ n) : PowerSeries k)) Filter.atTop
        (nhds (V : PowerSeries k)) ∧
      Filter.Tendsto (fun n => HahnSeries.ofPowerSeries ℤ k (U (φ n))) Filter.atTop
        (@nhds (LaurentSeries k) (LaurentSeries.orderTopology k)
          (HahnSeries.ofPowerSeries ℤ k V)) := by
  obtain ⟨V, φ, hφ, hconv⟩ := exists_subseq_tendsto_units_val U
  exact ⟨V, φ, hφ, hconv, tendsto_ofPowerSeries_orderTopology hconv⟩

end PowerSeries

namespace LaurentSeries

variable {k : Type*} [Field k]

/-- Removing the actual least Laurent degree leaves a power-series unit,
also when that least degree is negative. -/
theorem isUnit_powerSeriesPart (x : LaurentSeries k) (hx : x ≠ 0) :
    IsUnit x.powerSeriesPart := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa only [powerSeriesPart_coeff, Nat.cast_zero, add_zero] using
    (HahnSeries.coeff_order_eq_zero.not.mpr hx)

/-- The canonical power-series part gives an actual unit factorization
of every nonzero original Laurent series. -/
theorem exists_powerSeriesPart_unit_factor (x : LaurentSeries k) (hx : x ≠ 0) :
    ∃ U : (PowerSeries k)ˣ, (U : PowerSeries k) = x.powerSeriesPart ∧
      HahnSeries.single x.order 1 * HahnSeries.ofPowerSeries ℤ k U = x := by
  obtain ⟨U, hU⟩ := isUnit_powerSeriesPart x hx
  exact ⟨U, hU, by simpa only [hU] using single_order_mul_powerSeriesPart x⟩

/-- Normalizing any nonzero Laurent sequence by its actual least degree
produces a subsequence converging to an actual power-series unit. -/
theorem exists_subseq_powerSeriesPart_tendsto
    [TopologicalSpace k] [DiscreteTopology k] [Finite k]
    (x : ℕ → LaurentSeries k) (hx : ∀ n, x n ≠ 0) :
    ∃ U : (PowerSeries k)ˣ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => (x (φ n)).powerSeriesPart) Filter.atTop
        (nhds (U : PowerSeries k)) ∧
      Filter.Tendsto
        (fun n => HahnSeries.ofPowerSeries ℤ k (x (φ n)).powerSeriesPart) Filter.atTop
        (@nhds (LaurentSeries k) (orderTopology k) (HahnSeries.ofPowerSeries ℤ k U)) := by
  obtain ⟨V, ⟨U, hU⟩, φ, hφ, hconv⟩ :=
    PowerSeries.exists_subseq_tendsto_of_isUnit (fun n => (x n).powerSeriesPart)
      (fun n => isUnit_powerSeriesPart (x n) (hx n))
  have hconv' : Filter.Tendsto (fun n => (x (φ n)).powerSeriesPart) Filter.atTop
      (nhds (U : PowerSeries k)) := by
    simpa only [hU, Function.comp_def] using hconv
  exact ⟨U, φ, hφ, hconv', PowerSeries.tendsto_ofPowerSeries_orderTopology hconv'⟩

end LaurentSeries

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The actual normalized numerator in the approximate-invariant argument
converges under integer-exponent and power-series-unit approximation. -/
theorem tendsto_principalUnitPow_mul_subst_sub_of_intCast_tendsto
    {ι : Type*} {l : Filter ι} (q : (PowerSeries (ZMod p))ˣ)
    (hq : constantCoeff (q : PowerSeries (ZMod p)) = 1)
    (a : ι → ℤ) (c : PadicInt p)
    (ha : Filter.Tendsto (fun i => (a i : PadicInt p)) l (nhds c))
    {U : ι → PowerSeries (ZMod p)} {V : PowerSeries (ZMod p)}
    (hU : Filter.Tendsto U l (nhds V))
    (f : PowerSeries (ZMod p)) (hf : constantCoeff f = 0) :
    Filter.Tendsto
      (fun i => ((q ^ a i : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) *
        (U i).subst f - U i) l
      (nhds (principalUnitPow (q : PowerSeries (ZMod p)) hq c * V.subst f - V)) := by
  let : UniformSpace (ZMod p) := ⊥
  have hs : Continuous (fun z : PowerSeries (ZMod p) => z.subst f) :=
    MvPowerSeries.continuous_subst (HasSubst.of_constantCoeff_zero' hf).const
  simpa only [Function.comp_def] using
    ((tendsto_principalUnitPow_of_intCast_tendsto q hq a c ha).mul
      ((hs.tendsto V).comp hU)).sub hU

end PowerSeries

