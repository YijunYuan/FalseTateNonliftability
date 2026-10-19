module

public import FalseTateNonliftability.LaurentSeries.Taylor
public import FalseTateNonliftability.PowerSeries.UnitCompactness
public import FalseTateNonliftability.PowerSeries.UnitRigidity

/-!
# Valuations of actual approximate invariants

The original Laurent displacement is normalized by its actual integer order.
Compactness of the resulting power-series units and continuous p-adic powers
then give the limiting unit identity in Yuan, Lemma 4.1.
-/

@[expose] public section

noncomputable section

open scoped Topology PowerSeries.WithPiTopology

namespace LaurentSeries

/-- Multiplication by an actual signed monomial shifts every order
neighborhood exactly, including zero series and negative shifts. -/
theorem single_one_mul_mem_orderAddSubgroup_iff {R : Type*} [CommRing R]
    (m d : ℤ) (z : LaurentSeries R) :
    HahnSeries.single m 1 * z ∈ orderAddSubgroup (m + d) ↔ z ∈ orderAddSubgroup d := by
  rw [mem_orderAddSubgroup_iff_coeff, mem_orderAddSubgroup_iff_coeff]
  constructor
  · intro h j hj
    simpa only [HahnSeries.coeff_single_mul, one_mul, show m + j - m = j by omega] using
      h (m + j) (by omega)
  · intro h j hj
    simpa only [HahnSeries.coeff_single_mul, one_mul] using h (j - m) (by omega)

section Field

variable {k : Type*} [Field k]

local instance approximateInvariantsZeroSpanIsMaximal :
    (Ideal.span ({(0 : k)} : Set k)).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- On embedded power series, the actual Laurent coordinate `T*q`
acts by the original power-series substitution at `X*q`. -/
theorem subst_principalUnit_ofPowerSeries (q : (PowerSeries k)ˣ)
    (hq : PowerSeries.constantCoeff (q : PowerSeries k) = 1) (U : PowerSeries k) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (q : PowerSeries k))
        (principalUnitCoordinate_isAdmissible q hq) (HahnSeries.ofPowerSeries ℤ k U) =
      HahnSeries.ofPowerSeries ℤ k (U.subst (PowerSeries.X * (q : PowerSeries k))) := by
  have hzero : (PowerSeries.X * (q : PowerSeries k)).constantCoeff = 0 := by simp
  have hlinear : IsUnit ((PowerSeries.X * (q : PowerSeries k)).coeff 1) := by
    change IsUnit ((PowerSeries.X * (q : PowerSeries k)).coeff (0 + 1))
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hq]
    exact isUnit_one
  simpa only [map_mul, HahnSeries.ofPowerSeries_X] using
    subst_ofPowerSeries 0 IsNilpotent.zero _ hzero hlinear U

/-- The original displacement is the signed monomial times its actual
power-series normalized numerator. No nonnegative-order restriction is used. -/
theorem subst_principalUnit_sub_eq_single_mul (q : (PowerSeries k)ˣ)
    (hq : PowerSeries.constantCoeff (q : PowerSeries k) = 1) (x : LaurentSeries k) :
    subst 0 IsNilpotent.zero
        (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (q : PowerSeries k))
        (principalUnitCoordinate_isAdmissible q hq) x - x =
      HahnSeries.single x.order 1 * HahnSeries.ofPowerSeries ℤ k
        ((((q ^ x.order : (PowerSeries k)ˣ) : PowerSeries k) *
          x.powerSeriesPart.subst (PowerSeries.X * (q : PowerSeries k))) - x.powerSeriesPart) := by
  let E := subst 0 IsNilpotent.zero
    (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (q : PowerSeries k))
    (principalUnitCoordinate_isAdmissible q hq)
  change E x - x = _
  calc
    E x - x = E (HahnSeries.single x.order 1 *
        HahnSeries.ofPowerSeries ℤ k x.powerSeriesPart) -
          HahnSeries.single x.order 1 * HahnSeries.ofPowerSeries ℤ k x.powerSeriesPart := by
      rw [single_order_mul_powerSeriesPart]
    _ = _ := by
      dsimp only [E]
      rw [map_mul, subst_principalUnit_single q hq,
        subst_principalUnit_ofPowerSeries q hq, map_sub, map_mul]
      ring

/-- The original relative displacement bounds give zero convergence of
the actual normalized numerator in the named Laurent order topology. -/
theorem tendsto_normalized_subst_principalUnit_sub
    {ι : Type*} {l : Filter ι} (q : (PowerSeries k)ˣ)
    (hq : PowerSeries.constantCoeff (q : PowerSeries k) = 1)
    (x : ι → LaurentSeries k)
    (happrox : ∀ d : ℤ, ∀ᶠ i in l,
      subst 0 IsNilpotent.zero
          (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k (q : PowerSeries k))
          (principalUnitCoordinate_isAdmissible q hq) (x i) - x i ∈
        orderAddSubgroup ((x i).order + d)) :
    Filter.Tendsto
      (fun i => HahnSeries.ofPowerSeries ℤ k
        ((((q ^ (x i).order : (PowerSeries k)ˣ) : PowerSeries k) *
          (x i).powerSeriesPart.subst (PowerSeries.X * (q : PowerSeries k))) -
            (x i).powerSeriesPart)) l
      (@nhds (LaurentSeries k) (orderTopology k) 0) := by
  apply tendsto_orderTopology_iff.mpr
  intro d
  filter_upwards [happrox d] with i hi j hj
  have hnorm : HahnSeries.ofPowerSeries ℤ k
      ((((q ^ (x i).order : (PowerSeries k)ˣ) : PowerSeries k) *
        (x i).powerSeriesPart.subst (PowerSeries.X * (q : PowerSeries k))) -
          (x i).powerSeriesPart) ∈ orderAddSubgroup d := by
    apply (single_one_mul_mem_orderAddSubgroup_iff (x i).order d _).mp
    rwa [← subst_principalUnit_sub_eq_single_mul q hq (x i)]
  simpa only [HahnSeries.coeff_zero] using
    (mem_orderAddSubgroup_iff_coeff d _).mp hnorm j hj

end Field

section PrimeField

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] approximateInvariantsZeroSpanIsMaximal

/-- Compact normalized units and the original relative displacement bounds
produce the actual limiting unit identity, without an assumed identity. -/
theorem exists_unit_identity_of_approximate_invariance
    (q : (PowerSeries (ZMod p))ˣ)
    (hq : PowerSeries.constantCoeff (q : PowerSeries (ZMod p)) = 1)
    (x : ℕ → LaurentSeries (ZMod p)) (hx : ∀ n, x n ≠ 0) (c : PadicInt p)
    (hc : Filter.Tendsto (fun n => ((x n).order : PadicInt p)) Filter.atTop (nhds c))
    (happrox : ∀ d : ℤ, ∀ᶠ n in Filter.atTop,
      subst 0 IsNilpotent.zero
          (HahnSeries.single (1 : ℤ) 1 *
            HahnSeries.ofPowerSeries ℤ (ZMod p) (q : PowerSeries (ZMod p)))
          (principalUnitCoordinate_isAdmissible q hq) (x n) - x n ∈
        orderAddSubgroup ((x n).order + d)) :
    ∃ U : (PowerSeries (ZMod p))ˣ,
      PowerSeries.principalUnitPow (q : PowerSeries (ZMod p)) hq c *
        (U : PowerSeries (ZMod p)).subst (PowerSeries.X * (q : PowerSeries (ZMod p))) =
          (U : PowerSeries (ZMod p)) := by
  obtain ⟨U, φ, hφ, hconv, _⟩ := exists_subseq_powerSeriesPart_tendsto x hx
  have hc' : Filter.Tendsto (fun n => ((x (φ n)).order : PadicInt p)) Filter.atTop
      (nhds c) := by
    simpa only [Function.comp_def] using hc.comp hφ.tendsto_atTop
  have hlimit := PowerSeries.tendsto_principalUnitPow_mul_subst_sub_of_intCast_tendsto
    q hq (fun n => (x (φ n)).order) c hc' hconv
    (PowerSeries.X * (q : PowerSeries (ZMod p))) (by simp)
  have hzero := (tendsto_normalized_subst_principalUnit_sub q hq x happrox).comp
    hφ.tendsto_atTop
  let := orderTopology (ZMod p)
  let := orderTopology_t2Space (R := ZMod p)
  have heq : HahnSeries.ofPowerSeries ℤ (ZMod p)
      (PowerSeries.principalUnitPow (q : PowerSeries (ZMod p)) hq c *
        (U : PowerSeries (ZMod p)).subst (PowerSeries.X * (q : PowerSeries (ZMod p))) -
          (U : PowerSeries (ZMod p))) =
      (0 : LaurentSeries (ZMod p)) :=
    tendsto_nhds_unique (PowerSeries.tendsto_ofPowerSeries_orderTopology hlimit)
      (by simpa only [Function.comp_def] using hzero)
  refine ⟨U, sub_eq_zero.mp ?_⟩
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ZMod p)
  simpa only [map_zero] using heq

/-- **Valuations of actual approximate invariants** (Yuan, Lemma 4.1).
For an actual infinite-order tangent substitution, a p-adic limit of the
original Laurent orders must be zero when the relative displacements tend
to infinite order. Zero displacements and negative Laurent orders are retained. -/
theorem padic_limit_order_eq_zero_of_approximate_invariance
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (x : ℕ → LaurentSeries (ZMod p)) (hx : ∀ n, x n ≠ 0) (c : PadicInt p)
    (hc : Filter.Tendsto (fun n => ((x n).order : PadicInt p)) Filter.atTop (nhds c))
    (happrox : ∀ d : ℤ, ∀ᶠ n in Filter.atTop,
      powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
          (by rw [hlinear]; exact isUnit_one) (x n) - x n ∈
        orderAddSubgroup ((x n).order + d)) : c = 0 := by
  have hconst := PowerSeries.constantCoeff_divXPowOrder_of_tangent f hf hlinear
  have hunit : IsUnit f.divXPowOrder := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hconst]
    exact isUnit_one
  obtain ⟨q, hqeq⟩ := hunit
  have hq : PowerSeries.constantCoeff (q : PowerSeries (ZMod p)) = 1 := by
    simpa only [hqeq] using hconst
  have hfq : PowerSeries.X * (q : PowerSeries (ZMod p)) = f := by
    rw [hqeq]
    exact PowerSeries.X_mul_divXPowOrder_of_tangent f hf hlinear
  have hG : HahnSeries.single (1 : ℤ) 1 *
      HahnSeries.ofPowerSeries ℤ (ZMod p) (q : PowerSeries (ZMod p)) =
      HahnSeries.ofPowerSeries ℤ (ZMod p) f := by
    rw [← HahnSeries.ofPowerSeries_X, ← map_mul, hfq]
  have happrox' : ∀ d : ℤ, ∀ᶠ n in Filter.atTop,
      subst 0 IsNilpotent.zero
          (HahnSeries.single (1 : ℤ) 1 *
            HahnSeries.ofPowerSeries ℤ (ZMod p) (q : PowerSeries (ZMod p)))
          (principalUnitCoordinate_isAdmissible q hq) (x n) - x n ∈
        orderAddSubgroup ((x n).order + d) := by
    intro d
    filter_upwards [happrox d] with n hn
    simpa only [powerSeriesSubstEquiv_apply, hG] using hn
  obtain ⟨U, hidentity⟩ :=
    exists_unit_identity_of_approximate_invariance q hq x hx c hc happrox'
  apply PowerSeries.principalUnitPow_mul_subst_eq_implies_exponent_eq_zero
    f hf hlinear hinfinite (U : PowerSeries (ZMod p)) U.isUnit c
  simpa only [PowerSeries.principalUnitPow_eq_subst, hqeq,
    PowerSeries.X_mul_divXPowOrder_of_tangent f hf hlinear] using hidentity

end PrimeField

end LaurentSeries

