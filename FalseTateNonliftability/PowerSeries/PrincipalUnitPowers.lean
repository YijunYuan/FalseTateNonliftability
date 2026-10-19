module

public import FalseTateNonliftability.PowerSeries.PrincipalUnitIntegerPowers
public import FalseTateNonliftability.LaurentSeries.OrderTopology
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Instances.ZMod

/-!
# Continuous p-adic powers of actual principal units

Integral p-adic binomial coefficients are reduced modulo the prime before
substitution into the original power series. This realizes the continuous
powers in Yuan, Lemma 4.1, equation (4.2), on the usual power-series carrier.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The actual integral p-adic binomial series, reduced coefficientwise. -/
def padicBinomialSeries (c : PadicInt p) : PowerSeries (ZMod p) :=
  map PadicInt.toZMod (binomialSeries (PadicInt p) c)

@[simp]
theorem coeff_padicBinomialSeries (c : PadicInt p) (n : ℕ) :
    coeff n (padicBinomialSeries c) = PadicInt.toZMod (Ring.choose c n) := by
  simp [padicBinomialSeries]

@[simp]
theorem constantCoeff_padicBinomialSeries (c : PadicInt p) :
    constantCoeff (padicBinomialSeries c) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_padicBinomialSeries]
  simp

@[simp]
theorem padicBinomialSeries_natCast (n : ℕ) :
    padicBinomialSeries (n : PadicInt p) = (1 + X) ^ n := by
  simp [padicBinomialSeries]

@[simp]
theorem padicBinomialSeries_zero : padicBinomialSeries (0 : PadicInt p) = 1 := by
  simp [padicBinomialSeries]

theorem padicBinomialSeries_add (c d : PadicInt p) :
    padicBinomialSeries (c + d) = padicBinomialSeries c * padicBinomialSeries d := by
  simp [padicBinomialSeries]

private theorem hasSubst_sub_one (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) : HasSubst (z - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [hz])

/-- The p-adic power of an actual principal unit, obtained by substituting
its difference from one into the reduced integral binomial series. -/
def principalUnitPow (z : PowerSeries (ZMod p)) (hz : constantCoeff z = 1)
    (c : PadicInt p) : PowerSeries (ZMod p) :=
  substAlgHom (R := ZMod p) (a := z - 1)
    (HasSubst.of_constantCoeff_zero' (a := z - 1) (by simp [hz])) (padicBinomialSeries c)

theorem principalUnitPow_eq_subst (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) :
    principalUnitPow z hz c = (padicBinomialSeries c).subst (z - 1) :=
  congrFun (coe_substAlgHom (R := ZMod p) (hasSubst_sub_one z hz)) (padicBinomialSeries c)

@[simp]
theorem constantCoeff_principalUnitPow (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) :
    constantCoeff (principalUnitPow z hz c) = 1 := by
  rw [principalUnitPow_eq_subst]
  change MvPowerSeries.constantCoeff ((padicBinomialSeries c).subst (z - 1)) = 1
  rw [constantCoeff_subst_of_constantCoeff_zero (by
    change constantCoeff (z - 1) = 0
    simp [hz])]
  exact constantCoeff_padicBinomialSeries c

theorem isUnit_principalUnitPow (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) : IsUnit (principalUnitPow z hz c) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_principalUnitPow]
  exact isUnit_one

@[simp]
theorem principalUnitPow_natCast (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (n : ℕ) :
    principalUnitPow z hz (n : PadicInt p) = z ^ n := by
  simp only [principalUnitPow, padicBinomialSeries_natCast, map_pow, map_add, map_one,
    substAlgHom_X]
  congr 1
  ring

@[simp]
theorem principalUnitPow_zero (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) : principalUnitPow z hz 0 = 1 := by
  simp [principalUnitPow]

theorem principalUnitPow_add (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c d : PadicInt p) :
    principalUnitPow z hz (c + d) = principalUnitPow z hz c * principalUnitPow z hz d := by
  simp only [principalUnitPow, padicBinomialSeries_add, map_mul]

end PowerSeries

namespace HahnSeries

/-- The canonical power-series embedding preserves the least nonzero
degree, including infinite order for the zero series. -/
theorem orderTop_ofPowerSeries {R : Type*} [Semiring R] (z : PowerSeries R) :
    (ofPowerSeries ℤ R z).orderTop = WithTop.map (fun n : ℕ => (n : ℤ)) z.order := by
  rw [ofPowerSeries_apply, orderTop_embDomain]
  suffices h : (toPowerSeries.symm z).orderTop = z.order by rw [h]; rfl
  by_cases hz : z = 0
  · simp only [hz, map_zero, orderTop_zero, PowerSeries.order_zero]
    rfl
  rw [← PowerSeries.coe_toNat_order hz]
  apply orderTop_eq_of_le
  · exact (PowerSeries.coeff_order hz)
  · intro n hn
    have hle := PowerSeries.order_le n (show PowerSeries.coeff n z ≠ 0 from hn)
    rw [← PowerSeries.coe_toNat_order hz] at hle
    exact_mod_cast hle

end HahnSeries

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The actual residue homomorphism is locally constant and continuous
for the p-adic topology and the discrete residue-field topology. -/
theorem continuous_toZMod : Continuous (toZMod : PadicInt p → ZMod p) := by
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

variable {p : ℕ} [Fact p.Prime]

/-- Continuity is proved after reduction to the actual discrete coefficient
field, using continuity of the integral p-adic binomial coefficients. -/
theorem continuous_padicBinomialSeries :
    Continuous (padicBinomialSeries : PadicInt p → PowerSeries (ZMod p)) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (WithPiTopology.tendsto_iff_coeff_tendsto (ZMod p) _ _ _).mpr
  intro n
  simpa only [coeff_padicBinomialSeries, ContinuousAt, Function.comp_def] using
    (PadicInt.continuous_toZMod.comp (PadicInt.continuous_choose n)).continuousAt

/-- The original principal-unit power is continuous in its p-adic exponent. -/
theorem continuous_principalUnitPow (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) : Continuous (principalUnitPow z hz) := by
  let : UniformSpace (ZMod p) := ⊥
  have h : Continuous (fun f : PowerSeries (ZMod p) => f.subst (z - 1)) :=
    MvPowerSeries.continuous_subst (hasSubst_sub_one z hz).const
  change Continuous (fun c => principalUnitPow z hz c)
  simpa only [principalUnitPow_eq_subst, Function.comp_def] using
    h.comp continuous_padicBinomialSeries

@[simp]
theorem principalUnitPow_one (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) : principalUnitPow z hz 1 = z := by
  simpa only [Nat.cast_one, pow_one] using principalUnitPow_natCast z hz 1

@[simp]
theorem principalUnitPow_one_base (c : PadicInt p) :
    principalUnitPow (1 : PowerSeries (ZMod p)) (map_one _) c = 1 := by
  apply congrFun (PadicInt.denseRange_natCast.equalizer
    (continuous_principalUnitPow 1 (map_one _)) continuous_const ?_) c
  funext n
  simp only [Function.comp_apply, principalUnitPow_natCast, one_pow]

theorem principalUnitPow_mul_natCast (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) (n : ℕ) :
    principalUnitPow z hz (c * n) = principalUnitPow z hz c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, principalUnitPow_add, ih, pow_succ]

/-- The ordinary exponent law holds for both p-adic exponents, on the
same original principal unit and its actual power. -/
theorem principalUnitPow_mul (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c d : PadicInt p) :
    principalUnitPow z hz (c * d) =
      principalUnitPow (principalUnitPow z hz c) (constantCoeff_principalUnitPow z hz c) d := by
  apply congrFun (PadicInt.denseRange_natCast.equalizer
    ((continuous_principalUnitPow z hz).comp (continuous_const.mul continuous_id))
    (continuous_principalUnitPow _ (constantCoeff_principalUnitPow z hz c)) ?_) d
  funext n
  simp only [Function.comp_apply, Pi.mul_apply, id_eq,
    principalUnitPow_mul_natCast, principalUnitPow_natCast]

/-- Products of the actual original principal units commute with p-adic powering. -/
theorem principalUnitPow_mul_base (z w : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (hw : constantCoeff w = 1) (c : PadicInt p) :
    principalUnitPow (z * w) (by simp [hz, hw]) c =
      principalUnitPow z hz c * principalUnitPow w hw c := by
  apply congrFun (PadicInt.denseRange_natCast.equalizer
    (continuous_principalUnitPow _ (by simp [hz, hw]))
    ((continuous_principalUnitPow z hz).mul (continuous_principalUnitPow w hw)) ?_) c
  funext n
  simp only [Function.comp_apply, Pi.mul_apply, principalUnitPow_natCast, mul_pow]

theorem principalUnitPow_neg_mul (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) :
    principalUnitPow z hz (-c) * principalUnitPow z hz c = 1 := by
  rw [← principalUnitPow_add, neg_add_cancel, principalUnitPow_zero]

@[simp]
theorem coeff_one_padicBinomialSeries (c : PadicInt p) :
    coeff 1 (padicBinomialSeries c) = PadicInt.toZMod c := by
  simp

/-- A unit p-adic exponent preserves the exact order, including the
infinite order of the identity principal unit. -/
theorem order_principalUnitPow_sub_one_of_isUnit (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) (hc : IsUnit c) :
    (principalUnitPow z hz c - 1).order = (z - 1).order := by
  let Q : PowerSeries (ZMod p) := mk fun n => coeff (n + 1) (padicBinomialSeries c)
  have hQ : IsUnit Q := by
    rw [isUnit_iff_constantCoeff]
    simpa [Q] using hc.map PadicInt.toZMod
  have hfactor : padicBinomialSeries c - 1 = X * Q := by
    simpa only [constantCoeff_padicBinomialSeries, map_one] using
      sub_const_eq_X_mul_shift (padicBinomialSeries c)
  let E := substAlgHom (R := ZMod p) (hasSubst_sub_one z hz)
  have hdiff : principalUnitPow z hz c - 1 = E (padicBinomialSeries c - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [hdiff, hfactor, map_mul, substAlgHom_X, order_mul,
    order_zero_of_isUnit (hQ.map E), add_zero]

/-- The exact principal-unit order formula for every nonzero p-adic
exponent. The identity principal unit is retained through infinite order. -/
theorem order_principalUnitPow_sub_one (z : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (c : PadicInt p) (hc : c ≠ 0) :
    (principalUnitPow z hz c - 1).order =
      (p ^ c.valuation) • (z - 1).order := by
  let u := PadicInt.unitCoeff hc
  have hcp : c = (u : PadicInt p) * ((p ^ c.valuation : ℕ) : PadicInt p) := by
    simpa only [Nat.cast_pow] using PadicInt.unitCoeff_spec hc
  have hpower : principalUnitPow z hz c = principalUnitPow z hz (u : PadicInt p) ^
      (p ^ c.valuation) :=
    (congrArg (principalUnitPow z hz) hcp).trans
      (principalUnitPow_mul_natCast z hz (u : PadicInt p) (p ^ c.valuation))
  rw [hpower, order_pow_prime_pow_sub_one,
    order_principalUnitPow_sub_one_of_isUnit z hz (u : PadicInt p) u.isUnit]

/-- Integral exponents agree with powers in the actual power-series unit group. -/
theorem principalUnitPow_intCast (u : (PowerSeries (ZMod p))ˣ)
    (hu : constantCoeff (u : PowerSeries (ZMod p)) = 1) (n : ℤ) :
    principalUnitPow (u : PowerSeries (ZMod p)) hu (n : PadicInt p) =
      ((u ^ n : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) := by
  cases n with
  | ofNat a =>
      change principalUnitPow (u : PowerSeries (ZMod p)) hu ((a : ℤ) : PadicInt p) =
        ((u ^ (a : ℤ) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p))
      simpa only [Int.cast_natCast, zpow_natCast, Units.val_pow_eq_pow_val] using
        principalUnitPow_natCast (u : PowerSeries (ZMod p)) hu a
  | negSucc a =>
      change principalUnitPow (u : PowerSeries (ZMod p)) hu (-((a + 1 : ℕ) : PadicInt p)) =
        ((u ^ (-((a + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p))
      have hpos : principalUnitPow (u : PowerSeries (ZMod p)) hu
          ((a + 1 : ℕ) : PadicInt p) =
          ((u ^ (((a + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) := by
        simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using
          principalUnitPow_natCast (u : PowerSeries (ZMod p)) hu (a + 1)
      have hinv :
          ((u ^ (((a + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) *
            ((u ^ (-((a + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) = 1 := by
        rw [← Units.val_mul, ← zpow_add]
        simp
      calc
        _ = principalUnitPow (u : PowerSeries (ZMod p)) hu (-((a + 1 : ℕ) : PadicInt p)) *
            (((u ^ (((a + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)) *
              ((u ^ (-((a + 1 : ℕ) : ℤ)) : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p))) := by
                rw [hinv, mul_one]
        _ = _ := by
          rw [← mul_assoc, ← hpos, principalUnitPow_neg_mul, one_mul]

/-- Every integer approximation of the p-adic exponent converges to the
same explicit power in the actual power-series topology. -/
theorem tendsto_principalUnitPow_of_intCast_tendsto
    {ι : Type*} {l : Filter ι} (u : (PowerSeries (ZMod p))ˣ)
    (hu : constantCoeff (u : PowerSeries (ZMod p)) = 1)
    (a : ι → ℤ) (c : PadicInt p)
    (ha : Filter.Tendsto (fun i => (a i : PadicInt p)) l (nhds c)) :
    Filter.Tendsto (fun i => ((u ^ a i : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p)))
      l (nhds (principalUnitPow (u : PowerSeries (ZMod p)) hu c)) := by
  simpa only [Function.comp_def, principalUnitPow_intCast] using
    ((continuous_principalUnitPow (u : PowerSeries (ZMod p)) hu).tendsto c).comp ha

/-- Substitution at any zero-constant power series commutes with the
actual p-adic power. In particular this applies to every order-one coordinate. -/
theorem principalUnitPow_subst (z f : PowerSeries (ZMod p))
    (hz : constantCoeff z = 1) (hf : constantCoeff f = 0) (c : PadicInt p) :
    (principalUnitPow z hz c).subst f =
      principalUnitPow (z.subst f) (by
        change MvPowerSeries.constantCoeff (z.subst f) = 1
        rw [constantCoeff_subst_of_constantCoeff_zero hf]
        exact hz) c := by
  let hfs : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  rw [principalUnitPow_eq_subst, principalUnitPow_eq_subst,
    subst_comp_subst_apply (hasSubst_sub_one z hz) hfs]
  congr 1
  rw [subst_sub hfs]
  congr 1
  exact (congrFun (coe_substAlgHom (R := ZMod p) hfs) 1).symm.trans
    (map_one (substAlgHom (R := ZMod p) hfs))

/-- For power series over a discrete coefficient ring, coefficientwise
convergence implies Laurent order convergence. The common nonnegative support
makes each required initial segment finite. -/
theorem tendsto_ofPowerSeries_orderTopology
    {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {ι : Type*} {l : Filter ι} {f : ι → PowerSeries R} {g : PowerSeries R}
    (h : Filter.Tendsto f l (nhds g)) :
    Filter.Tendsto (fun i => HahnSeries.ofPowerSeries ℤ R (f i)) l
      (@nhds (LaurentSeries R) (LaurentSeries.orderTopology R)
        (HahnSeries.ofPowerSeries ℤ R g)) := by
  have hc := (WithPiTopology.tendsto_iff_coeff_tendsto R f l g).mp h
  have hfinite : ∀ N : ℕ, ∀ᶠ i in l, ∀ n < N, coeff n (f i) = coeff n g := by
    intro N
    induction N with
    | zero => exact Filter.Eventually.of_forall (by intro i n hn; omega)
    | succ N ih =>
        have hs : ({coeff N g} : Set R) ∈ nhds (coeff N g) := by
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

/-- The integer-power limit is also the limit in the named Laurent order
topology, on the actual Laurent-series carrier. -/
theorem tendsto_ofPowerSeries_principalUnitPow_of_intCast_tendsto
    {ι : Type*} {l : Filter ι} (u : (PowerSeries (ZMod p))ˣ)
    (hu : constantCoeff (u : PowerSeries (ZMod p)) = 1)
    (a : ι → ℤ) (c : PadicInt p)
    (ha : Filter.Tendsto (fun i => (a i : PadicInt p)) l (nhds c)) :
    Filter.Tendsto
      (fun i => HahnSeries.ofPowerSeries ℤ (ZMod p)
        ((u ^ a i : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p))) l
      (@nhds (LaurentSeries (ZMod p)) (LaurentSeries.orderTopology (ZMod p))
        (HahnSeries.ofPowerSeries ℤ (ZMod p)
          (principalUnitPow (u : PowerSeries (ZMod p)) hu c))) :=
  tendsto_ofPowerSeries_orderTopology
    (tendsto_principalUnitPow_of_intCast_tendsto u hu a c ha)

/-- Along any nontrivial approximation filter, the actual Laurent limit
is uniquely the explicit principal-unit power. -/
theorem eq_ofPowerSeries_principalUnitPow_of_intCast_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] (u : (PowerSeries (ZMod p))ˣ)
    (hu : constantCoeff (u : PowerSeries (ZMod p)) = 1)
    (a : ι → ℤ) (c : PadicInt p)
    (ha : Filter.Tendsto (fun i => (a i : PadicInt p)) l (nhds c))
    (g : LaurentSeries (ZMod p))
    (hg : Filter.Tendsto
      (fun i => HahnSeries.ofPowerSeries ℤ (ZMod p)
        ((u ^ a i : (PowerSeries (ZMod p))ˣ) : PowerSeries (ZMod p))) l
      (@nhds (LaurentSeries (ZMod p)) (LaurentSeries.orderTopology (ZMod p)) g)) :
    g = HahnSeries.ofPowerSeries ℤ (ZMod p)
      (principalUnitPow (u : PowerSeries (ZMod p)) hu c) := by
  let := LaurentSeries.orderTopology (ZMod p)
  let := LaurentSeries.orderTopology_t2Space (R := ZMod p)
  exact tendsto_nhds_unique hg
    (tendsto_ofPowerSeries_principalUnitPow_of_intCast_tendsto u hu a c ha)

end PowerSeries
