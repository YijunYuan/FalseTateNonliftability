/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.Mathlib.NumberTheory.Padics.Continuity
public import FalseTateNonliftability.Mathlib.RingTheory.LaurentSeries.Topology
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Compactness
public import FalseTateNonliftability.Mathlib.RingTheory.PowerSeries.Composition
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Instances.ZMod

/-!
# Powers of principal units of `κ⟦T⟧` in characteristic `p`

Let `κ` be a field of characteristic `p` and `z ∈ κ⟦T⟧`. Then
`z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r)`, so `v_T(z ^ (p ^ r) - 1) = p ^ r v_T(z - 1)`; and if `z` is a
principal unit and `p ∤ a`, then `v_T(z ^ a - 1) = v_T(z - 1)`.

For a principal unit `z ∈ 1 + T κ⟦T⟧` and `c ∈ ℤ_p`, the power
`z ^ c := ∑ₙ (c choose n) (z - 1) ^ n` is obtained by substituting `z - 1` into the image in
`κ⟦X⟧` of the binomial series `(1 + X) ^ c ∈ ℤ_p⟦X⟧`. It agrees with the power `z ^ n` for
`n ∈ ℤ`, depends continuously on `c`, satisfies the exponent laws, commutes with substitution,
and `v_T(z ^ c - 1) = v_T(z - 1)` for `c ∈ ℤ_pˣ`.

Let `κ` carry the discrete topology. If `κ` is finite, then for nonzero `x n ∈ κ((T))` the units
`T ^ (-v_T(x n)) x n` of `κ⟦T⟧` have a subsequence converging to a unit. The expressions
`u ^ (a i) (U i ∘ f) - U i` converge to `u ^ c (V ∘ f) - V` when `a i → c` in `ℤ_p` and `U i → V`.

## Main definitions

* `PowerSeries.padicBinomialSeries κ c`: the image in `κ⟦X⟧` of `(1 + X) ^ c ∈ ℤ_p⟦X⟧`.
* `PowerSeries.principalUnitPow z c`: the power `z ^ c` of a principal unit `z` by `c ∈ ℤ_p`.

## Main results

* `PowerSeries.order_pow_prime_pow_sub_one`: `v_T(z ^ (p ^ r) - 1) = p ^ r • v_T(z - 1)`.
* `PowerSeries.order_pow_sub_one_of_not_dvd`: `v_T(z ^ a - 1) = v_T(z - 1)` if `z(0) = 1` and
  `p ∤ a`.
* `PowerSeries.principalUnitPow_natCast`, `PowerSeries.principalUnitPow_intCast`: `z ^ n` for
  `n ∈ ℤ`.
* `PowerSeries.principalUnitPow_add`, `PowerSeries.principalUnitPow_mul_natCast`,
  `PowerSeries.principalUnitPow_mul_base`: exponent laws.
* `PowerSeries.continuous_principalUnitPow`: `c ↦ z ^ c` is continuous.
* `PowerSeries.order_principalUnitPow_sub_one_of_isUnit`: `v_T(z ^ c - 1) = v_T(z - 1)` for
  `c ∈ ℤ_pˣ`.
* `PowerSeries.principalUnitPow_subst`: `z ^ c ∘ f = (z ∘ f) ^ c` for `f(0) = 0`.
* `LaurentSeries.exists_subseq_powerSeriesPart_tendsto`: for nonzero `x n ∈ κ((T))`, the units
  `T ^ (-v_T(x n)) x n` have a subsequence converging to a unit of `κ⟦T⟧`.
* `PowerSeries.tendsto_principalUnitPow_mul_subst_sub_of_intCast_tendsto`: continuity of
  `(c, U) ↦ u ^ c (U ∘ f) - U` along integer approximations of `c`.

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.1 and Lemma 4.2, equation (4.3).
-/

@[expose] public section

noncomputable section

/-! ### Natural powers -/

section NatPowers

namespace PowerSeries

variable {κ : Type*} [Field κ] {p : ℕ} [CharP κ p]

/-- In characteristic `p`, `z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r)`. -/
theorem pow_prime_pow_sub_one [Fact p.Prime] (z : PowerSeries κ) (r : ℕ) :
    z ^ (p ^ r) - 1 = (z - 1) ^ (p ^ r) := by
  have : CharP (PowerSeries κ) p := charP_of_injective_ringHom C_injective p
  simpa using (sub_pow_char_pow (p := p) z 1 r).symm

/-- In characteristic `p`, `v_T(z ^ (p ^ r) - 1) = p ^ r • v_T(z - 1)`. -/
theorem order_pow_prime_pow_sub_one [Fact p.Prime] (z : PowerSeries κ) (r : ℕ) :
    (z ^ (p ^ r) - 1).order = (p ^ r) • (z - 1).order := by
  rw [pow_prime_pow_sub_one, order_pow]

/-- If `z(0) = 1` and `p ∤ a`, then `v_T(z ^ a - 1) = v_T(z - 1)`. -/
theorem order_pow_sub_one_of_not_dvd (z : PowerSeries κ) (hz : constantCoeff z = 1) (a : ℕ)
    (ha : ¬ p ∣ a) : (z ^ a - 1).order = (z - 1).order := by
  have hsum : IsUnit (∑ i ∈ Finset.range a, z ^ i) := by
    rw [isUnit_iff_constantCoeff]
    simpa [map_sum, hz] using
      (isUnit_iff_ne_zero.mpr (mt (CharP.cast_eq_zero_iff κ p a).mp ha) : IsUnit (a : κ))
  rw [← mul_geom_sum, order_mul, order_zero_of_isUnit hsum, add_zero]

end PowerSeries

end NatPowers

/-! ### `p`-adic powers -/

section PadicPowers

namespace PowerSeries

open scoped Topology PowerSeries.WithPiTopology

variable {κ : Type*} [Field κ] {p : ℕ} [Fact p.Prime] [CharP κ p]

section BinomialSeries

variable (κ) in
/-- The image in `κ⟦X⟧` of the binomial series `(1 + X) ^ c = ∑ₙ (c choose n) X ^ n ∈ ℤ_p⟦X⟧`
of `c ∈ ℤ_p`. -/
def padicBinomialSeries (c : ℤ_[p]) : PowerSeries κ :=
  map ((ZMod.castHom dvd_rfl κ).comp PadicInt.toZMod) (binomialSeries ℤ_[p] c)

@[simp]
theorem coeff_padicBinomialSeries (c : ℤ_[p]) (n : ℕ) :
    coeff n (padicBinomialSeries κ c) = ((PadicInt.toZMod (Ring.choose c n)).cast : κ) := by
  simp [padicBinomialSeries]

@[simp]
theorem constantCoeff_padicBinomialSeries (c : ℤ_[p]) :
    constantCoeff (padicBinomialSeries κ c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_padicBinomialSeries]
  simp

@[simp]
theorem padicBinomialSeries_natCast (n : ℕ) :
    padicBinomialSeries κ (n : ℤ_[p]) = (1 + X) ^ n := by
  simp [padicBinomialSeries]

theorem padicBinomialSeries_add (c d : ℤ_[p]) :
    padicBinomialSeries κ (c + d) = padicBinomialSeries κ c * padicBinomialSeries κ d := by
  simp [padicBinomialSeries]

/-- `c ↦ (1 + X) ^ c` is continuous from `ℤ_p` to `κ⟦X⟧` for the discrete topology on `κ`. -/
theorem continuous_padicBinomialSeries [TopologicalSpace κ] [DiscreteTopology κ] :
    Continuous (padicBinomialSeries κ : ℤ_[p] → PowerSeries κ) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (WithPiTopology.tendsto_iff_coeff_tendsto κ _ _ _).mpr
  intro n
  simpa only [coeff_padicBinomialSeries, ContinuousAt, Function.comp_def] using
    ((continuous_of_discreteTopology (f := (ZMod.cast : ZMod p → κ))).comp
      (PadicInt.continuous_toZMod.comp (PadicInt.continuous_choose n))).continuousAt

end BinomialSeries

/-- The power `z ^ c = ∑ₙ (c choose n) (z - 1) ^ n` of a principal unit `z ∈ 1 + T κ⟦T⟧` by
`c ∈ ℤ_p`, the substitution of `z - 1` into `padicBinomialSeries κ c`. -/
def principalUnitPow (z : PowerSeries κ) (c : ℤ_[p]) : PowerSeries κ :=
  (padicBinomialSeries κ c).subst (z - 1)

theorem principalUnitPow_eq_subst (z : PowerSeries κ) (c : ℤ_[p]) :
    principalUnitPow z c = (padicBinomialSeries κ c).subst (z - 1) :=
  rfl

section Algebra

variable {z : PowerSeries κ}

private theorem hasSubst_sub_one (hz : constantCoeff z = 1) : HasSubst (z - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [hz])

private theorem principalUnitPow_eq_substAlgHom (hz : constantCoeff z = 1) (c : ℤ_[p]) :
    principalUnitPow z c = substAlgHom (R := κ) (hasSubst_sub_one hz) (padicBinomialSeries κ c) :=
  (congrFun (coe_substAlgHom (R := κ) (hasSubst_sub_one hz)) (padicBinomialSeries κ c)).symm

@[simp]
theorem principalUnitPow_natCast (hz : constantCoeff z = 1) (n : ℕ) :
    principalUnitPow z (n : ℤ_[p]) = z ^ n := by
  rw [principalUnitPow_eq_substAlgHom hz, padicBinomialSeries_natCast, map_pow, map_add, map_one,
    substAlgHom_X]
  congr 1
  ring

@[simp]
theorem principalUnitPow_zero (hz : constantCoeff z = 1) :
    principalUnitPow z (0 : ℤ_[p]) = 1 := by
  simpa using principalUnitPow_natCast (p := p) hz 0

@[simp]
theorem principalUnitPow_one (hz : constantCoeff z = 1) : principalUnitPow z (1 : ℤ_[p]) = z := by
  simpa using principalUnitPow_natCast (p := p) hz 1

theorem principalUnitPow_add (hz : constantCoeff z = 1) (c d : ℤ_[p]) :
    principalUnitPow z (c + d) = principalUnitPow z c * principalUnitPow z d := by
  simp only [principalUnitPow_eq_substAlgHom hz, padicBinomialSeries_add, map_mul]

theorem principalUnitPow_neg_mul (hz : constantCoeff z = 1) (c : ℤ_[p]) :
    principalUnitPow z (-c) * principalUnitPow z c = 1 := by
  rw [← principalUnitPow_add hz, neg_add_cancel, principalUnitPow_zero hz]

theorem principalUnitPow_mul_natCast (hz : constantCoeff z = 1) (c : ℤ_[p]) (n : ℕ) :
    principalUnitPow z (c * (n : ℤ_[p])) = principalUnitPow z c ^ n := by
  induction n with
  | zero => simp [principalUnitPow_zero hz]
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, principalUnitPow_add hz, ih, pow_succ]

@[simp]
theorem principalUnitPow_one_base (c : ℤ_[p]) : principalUnitPow (1 : PowerSeries κ) c = 1 := by
  rw [principalUnitPow_eq_subst, sub_self, subst_zero_eq_C_constantCoeff,
    constantCoeff_padicBinomialSeries]
  simp

/-- For a principal unit `u` of `κ⟦T⟧` and `n ∈ ℤ`, `principalUnitPow u n` is the power `u ^ n` in
the unit group. -/
theorem principalUnitPow_intCast (u : (PowerSeries κ)ˣ)
    (hu : constantCoeff (u : PowerSeries κ) = 1) (n : ℤ) :
    principalUnitPow (u : PowerSeries κ) (n : ℤ_[p]) =
      ((u ^ n : (PowerSeries κ)ˣ) : PowerSeries κ) := by
  cases n with
  | ofNat a =>
      simpa only [Int.ofNat_eq_natCast, Int.cast_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
        using principalUnitPow_natCast (p := p) hu a
  | negSucc a =>
      have hpos : principalUnitPow (u : PowerSeries κ) ((a + 1 : ℕ) : ℤ_[p]) =
          ((u ^ (((a + 1 : ℕ) : ℤ)) : (PowerSeries κ)ˣ) : PowerSeries κ) := by
        simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using
          principalUnitPow_natCast (p := p) hu (a + 1)
      have hinv : ((u ^ (((a + 1 : ℕ) : ℤ)) : (PowerSeries κ)ˣ) : PowerSeries κ) *
          ((u ^ Int.negSucc a : (PowerSeries κ)ˣ) : PowerSeries κ) = 1 := by
        rw [← Units.val_mul, ← zpow_add, Int.negSucc_eq]
        simp
      have hcast : ((Int.negSucc a : ℤ) : ℤ_[p]) = -((a + 1 : ℕ) : ℤ_[p]) := by
        rw [Int.negSucc_eq]
        push_cast
        ring
      calc
        _ = principalUnitPow (u : PowerSeries κ) (-((a + 1 : ℕ) : ℤ_[p])) *
            (((u ^ (((a + 1 : ℕ) : ℤ)) : (PowerSeries κ)ˣ) : PowerSeries κ) *
              ((u ^ Int.negSucc a : (PowerSeries κ)ˣ) : PowerSeries κ)) := by
          rw [hinv, mul_one, hcast]
        _ = _ := by
          rw [← mul_assoc, ← hpos, principalUnitPow_neg_mul hu, one_mul]

/-- For `f(0) = 0`, `(z ^ c) ∘ f = (z ∘ f) ^ c`. -/
theorem principalUnitPow_subst {f : PowerSeries κ} (hz : constantCoeff z = 1)
    (hf : constantCoeff f = 0) (c : ℤ_[p]) :
    (principalUnitPow z c).subst f = principalUnitPow (z.subst f) c := by
  let hfs : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  rw [principalUnitPow_eq_subst, principalUnitPow_eq_subst,
    subst_comp_subst_apply (hasSubst_sub_one hz) hfs, subst_sub hfs]
  congr 2
  exact (congrFun (coe_substAlgHom (R := κ) hfs) 1).symm.trans
    (map_one (substAlgHom (R := κ) hfs))

/-- If `c ∈ ℤ_p` is a unit, then `v_T(z ^ c - 1) = v_T(z - 1)`. -/
theorem order_principalUnitPow_sub_one_of_isUnit (hz : constantCoeff z = 1) {c : ℤ_[p]}
    (hc : IsUnit c) : (principalUnitPow z c - 1).order = (z - 1).order := by
  let Q : PowerSeries κ := mk fun n ↦ coeff (n + 1) (padicBinomialSeries κ c)
  have hQ : IsUnit Q := by
    rw [isUnit_iff_constantCoeff]
    simpa [Q] using hc.map ((ZMod.castHom dvd_rfl κ).comp PadicInt.toZMod)
  have hfactor : padicBinomialSeries κ c - 1 = X * Q := by
    simpa only [constantCoeff_padicBinomialSeries, map_one] using
      sub_const_eq_X_mul_shift (padicBinomialSeries κ c)
  let E := substAlgHom (R := κ) (hasSubst_sub_one hz)
  have hdiff : principalUnitPow z c - 1 = E (padicBinomialSeries κ c - 1) := by
    rw [map_sub, map_one, ← principalUnitPow_eq_substAlgHom hz]
  rw [hdiff, hfactor, map_mul, substAlgHom_X, order_mul, order_zero_of_isUnit (hQ.map E),
    add_zero]

end Algebra

section Topology

variable [TopologicalSpace κ] [DiscreteTopology κ] {z : PowerSeries κ}

/-- For a principal unit `z`, `c ↦ z ^ c` is continuous from `ℤ_p` to `κ⟦T⟧` for the discrete
topology on `κ`. -/
theorem continuous_principalUnitPow (hz : constantCoeff z = 1) :
    Continuous (principalUnitPow z : ℤ_[p] → PowerSeries κ) :=
  (continuous_subst_of_constantCoeff_zero (by simp [hz])).comp continuous_padicBinomialSeries

/-- If integers `a i` converge to `c` in `ℤ_p`, then `u ^ (a i)` converges to `u ^ c` in `κ⟦T⟧`. -/
theorem tendsto_principalUnitPow_of_intCast_tendsto {ι : Type*} {l : Filter ι}
    (u : (PowerSeries κ)ˣ) (hu : constantCoeff (u : PowerSeries κ) = 1) {a : ι → ℤ}
    {c : ℤ_[p]} (ha : Filter.Tendsto (fun i ↦ (a i : ℤ_[p])) l (𝓝 c)) :
    Filter.Tendsto (fun i ↦ ((u ^ a i : (PowerSeries κ)ˣ) : PowerSeries κ)) l
      (𝓝 (principalUnitPow (u : PowerSeries κ) c)) := by
  simpa only [Function.comp_def, principalUnitPow_intCast u hu] using
    ((continuous_principalUnitPow hu).tendsto c).comp ha

end Topology

/-- For principal units `z` and `w`, `(z * w) ^ c = z ^ c * w ^ c`. -/
theorem principalUnitPow_mul_base {z w : PowerSeries κ} (hz : constantCoeff z = 1)
    (hw : constantCoeff w = 1) (c : ℤ_[p]) :
    principalUnitPow (z * w) c = principalUnitPow z c * principalUnitPow w c := by
  let : TopologicalSpace κ := ⊥
  have : DiscreteTopology κ := ⟨rfl⟩
  have hzw : constantCoeff (z * w) = 1 := by simp [hz, hw]
  apply congrFun (PadicInt.denseRange_natCast.equalizer (continuous_principalUnitPow hzw)
    ((continuous_principalUnitPow hz).mul (continuous_principalUnitPow hw)) ?_) c
  funext n
  simp only [Function.comp_apply, Pi.mul_apply, principalUnitPow_natCast hzw,
    principalUnitPow_natCast hz, principalUnitPow_natCast hw, mul_pow]

end PowerSeries

end PadicPowers

/-! ### Limits of normalized Laurent series -/

section Limits

open scoped Topology PowerSeries.WithPiTopology LaurentSeries.OrderTopology

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
        (𝓝 (HahnSeries.ofPowerSeries ℤ κ U)) := by
  obtain ⟨V, ⟨U, hU⟩, φ, hφ, hconv⟩ :=
    PowerSeries.exists_subseq_tendsto_of_isUnit (fun n ↦ (x n).powerSeriesPart)
      (fun n ↦ isUnit_powerSeriesPart (hx n))
  have hconv' : Filter.Tendsto (fun n ↦ (x (φ n)).powerSeriesPart) Filter.atTop
      (𝓝 (U : PowerSeries κ)) := by
    simpa only [hU, Function.comp_def] using hconv
  exact ⟨U, φ, hφ, hconv', (continuous_ofPowerSeries.tendsto _).comp hconv'⟩

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

end Limits
