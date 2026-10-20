/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.PowerSeries.PrincipalUnitIntegerPowers
public import FalseTateNonliftability.LaurentSeries.OrderTopology
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Instances.ZMod

/-!
# `p`-adic powers of principal units of `κ⟦T⟧`

Let `κ` be a field of characteristic `p`, let `z ∈ 1 + T κ⟦T⟧` be a principal unit and let
`c ∈ ℤ_p`. The power `z ^ c := ∑ₙ (c choose n) (z - 1) ^ n` is obtained by substituting `z - 1`
into the image in `κ⟦X⟧` of the binomial series `(1 + X) ^ c ∈ ℤ_p⟦X⟧`. It agrees with the power
`z ^ n` for `n ∈ ℤ`, depends continuously on `c`, satisfies the exponent laws, commutes with
substitution, and `v_T(z ^ c - 1) = p ^ v_p(c) v_T(z - 1)` for `c ≠ 0`.

## Main definitions

* `PowerSeries.padicBinomialSeries κ c`: the image in `κ⟦X⟧` of `(1 + X) ^ c ∈ ℤ_p⟦X⟧`.
* `PowerSeries.principalUnitPow z c`: the power `z ^ c` of a principal unit `z` by `c ∈ ℤ_p`.

## Main results

* `PowerSeries.principalUnitPow_natCast`, `PowerSeries.principalUnitPow_intCast`: `z ^ n` for
  `n ∈ ℤ`.
* `PowerSeries.principalUnitPow_add`, `PowerSeries.principalUnitPow_mul_natCast`,
  `PowerSeries.principalUnitPow_mul_base`: exponent laws.
* `PowerSeries.continuous_principalUnitPow`: `c ↦ z ^ c` is continuous.
* `PowerSeries.order_principalUnitPow_sub_one`: `v_T(z ^ c - 1) = p ^ v_p(c) v_T(z - 1)`.
* `PowerSeries.principalUnitPow_subst`: `z ^ c ∘ f = (z ∘ f) ^ c` for `f(0) = 0`.

## References

* Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  Lemma 4.2, equation (4.3).
-/

@[expose] public section

noncomputable section

namespace HahnSeries

/-- The order of `z ∈ R⟦T⟧` as a Laurent series is its order as a power series. -/
theorem orderTop_ofPowerSeries {R : Type*} [Semiring R] (z : PowerSeries R) :
    (ofPowerSeries ℤ R z).orderTop = WithTop.map (fun n : ℕ ↦ (n : ℤ)) z.order := by
  rw [ofPowerSeries_apply, orderTop_embDomain]
  suffices h : (toPowerSeries.symm z).orderTop = z.order by rw [h]; rfl
  by_cases hz : z = 0
  · simp only [hz, map_zero, orderTop_zero, PowerSeries.order_zero]
    rfl
  rw [← PowerSeries.coe_toNat_order hz]
  apply orderTop_eq_of_le
  · exact PowerSeries.coeff_order hz
  · intro n hn
    have hle := PowerSeries.order_le n (show PowerSeries.coeff n z ≠ 0 from hn)
    rw [← PowerSeries.coe_toNat_order hz] at hle
    exact_mod_cast hle

end HahnSeries

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The reduction `ℤ_p → ℤ/pℤ` is continuous. -/
theorem continuous_toZMod : Continuous (toZMod : ℤ_[p] → ZMod p) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have heq : ∀ᶠ y in nhds x, toZMod y = toZMod x := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    apply sub_eq_zero.mp
    rw [← map_sub, ← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
    exact (norm_lt_one_iff_dvd _).mp (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  apply tendsto_const_nhds.congr'
  filter_upwards [heq] with y hy
  exact hy.symm

end PadicInt

namespace PowerSeries

open scoped Topology PowerSeries.WithPiTopology

section Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

/-- Substitution of a power series `a` with `a(0) = 0` is continuous for the `T`-adic topology. -/
theorem continuous_subst_of_constantCoeff_zero {a : PowerSeries R} (ha : constantCoeff a = 0) :
    Continuous (fun f : PowerSeries R ↦ (f.subst a : PowerSeries R)) := by
  obtain rfl := DiscreteTopology.eq_bot (α := R)
  let : UniformSpace R := ⊥
  exact MvPowerSeries.continuous_subst (HasSubst.of_constantCoeff_zero' ha).const

/-- For power series over a discrete ring, coefficientwise convergence implies convergence of
the corresponding Laurent series in the `T`-adic topology. -/
theorem tendsto_ofPowerSeries_orderTopology {ι : Type*} {l : Filter ι} {f : ι → PowerSeries R}
    {g : PowerSeries R} (h : Filter.Tendsto f l (𝓝 g)) :
    Filter.Tendsto (fun i ↦ HahnSeries.ofPowerSeries ℤ R (f i)) l
      (@nhds (LaurentSeries R) (LaurentSeries.orderTopology R)
        (HahnSeries.ofPowerSeries ℤ R g)) := by
  have hc := (WithPiTopology.tendsto_iff_coeff_tendsto R f l g).mp h
  have hfinite : ∀ N : ℕ, ∀ᶠ i in l, ∀ n < N, coeff n (f i) = coeff n g := by
    intro N
    induction N with
    | zero => exact Filter.Eventually.of_forall (by intro i n hn; omega)
    | succ N ih =>
        have hs : ({coeff N g} : Set R) ∈ 𝓝 (coeff N g) := by
          simp [nhds_discrete]
        have hN : ∀ᶠ i in l, coeff N (f i) = coeff N g := by
          simpa only [Set.mem_singleton_iff] using (hc N).eventually hs
        filter_upwards [ih, hN] with i hi hiN n hn
        by_cases hEq : n = N
        · simpa only [hEq] using hiN
        · exact hi n (by omega)
  apply LaurentSeries.tendsto_orderTopology_iff.mpr
  intro m
  filter_upwards [hfinite (m.toNat + 1)] with i hi j hj
  by_cases hjneg : j < 0
  · simp only [coeff_coe, ite_eq_left hjneg]
  · lift j to ℕ using le_of_not_gt hjneg
    simpa only [HahnSeries.ofPowerSeries_apply_coeff] using hi j (by omega)

end Topology

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

@[simp]
theorem padicBinomialSeries_zero : padicBinomialSeries κ (0 : ℤ_[p]) = 1 := by
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
theorem constantCoeff_principalUnitPow (hz : constantCoeff z = 1) (c : ℤ_[p]) :
    constantCoeff (principalUnitPow z c) = 1 := by
  change MvPowerSeries.constantCoeff ((padicBinomialSeries κ c).subst (z - 1)) = 1
  rw [constantCoeff_subst_of_constantCoeff_zero (by
    change constantCoeff (z - 1) = 0
    simp [hz])]
  exact constantCoeff_padicBinomialSeries c

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

/-- If `c ∈ ℤ_p` is nonzero, then `v_T(z ^ c - 1) = p ^ v_p(c) v_T(z - 1)`. -/
theorem order_principalUnitPow_sub_one (hz : constantCoeff z = 1) {c : ℤ_[p]} (hc : c ≠ 0) :
    (principalUnitPow z c - 1).order = (p ^ c.valuation) • (z - 1).order := by
  let u := PadicInt.unitCoeff hc
  have hcp : c = (u : ℤ_[p]) * ((p ^ c.valuation : ℕ) : ℤ_[p]) := by
    simpa only [Nat.cast_pow] using PadicInt.unitCoeff_spec hc
  have hpower : principalUnitPow z c = principalUnitPow z (u : ℤ_[p]) ^ (p ^ c.valuation) :=
    (congrArg (principalUnitPow z) hcp).trans
      (principalUnitPow_mul_natCast hz (u : ℤ_[p]) (p ^ c.valuation))
  rw [hpower, order_pow_prime_pow_sub_one, order_principalUnitPow_sub_one_of_isUnit hz u.isUnit]

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
