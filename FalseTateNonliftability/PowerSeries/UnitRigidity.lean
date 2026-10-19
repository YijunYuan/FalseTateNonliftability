module

public import FalseTateNonliftability.PowerSeries.PrincipalUnitPowers
public import FalseTateNonliftability.LaurentSeries.IterateGrowth
public import FalseTateNonliftability.LaurentSeries.FrobeniusKernel
public import Mathlib.Algebra.CharP.Reduced

/-!
# Rigidity of an actual principal-unit identity

For an infinite-order substitution tangent to the identity over the prime
field, an identity `(f/T)^m * (U ∘ f) = U` with a power-series unit forces
the p-adic exponent `m` to be zero. The ratios use the canonical
`PowerSeries.divXPowOrder`; the cocycle and all growth estimates are proved
for the original iterates.

This proves `nl:unit-identity-rigidity`, following Yuan, Lemma 4.1,
equations (4.3)–(4.4). Every prime, including `2`, is allowed.
-/

@[expose] public section

noncomputable section

namespace PowerSeries

open LaurentSeries

variable {p : ℕ} [Fact p.Prime]

local instance unitRigidityZeroSpanIsMaximal :
    (Ideal.span ({(0 : ZMod p)} : Set (ZMod p))).IsMaximal := by
  rw [Ideal.span_singleton_zero]
  exact Ideal.bot_isMaximal

/-- A series tangent to the identity has actual power-series order one. -/
theorem order_eq_one_of_tangent (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) : f.order = 1 := by
  apply order_eq_nat.mpr
  refine ⟨by rw [hlinear]; exact one_ne_zero, ?_⟩
  intro n hn
  have hn0 : n = 0 := by omega
  simpa only [hn0, coeff_zero_eq_constantCoeff_apply] using hf

/-- The canonical quotient by the leading variable is an actual principal unit. -/
theorem constantCoeff_divXPowOrder_of_tangent (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) :
    f.divXPowOrder.constantCoeff = 1 := by
  rw [constantCoeff_divXPowOrder, order_eq_one_of_tangent f hf hlinear]
  simpa using hlinear

/-- The canonical ratio `f/T` has exactly the original numerator. -/
theorem X_mul_divXPowOrder_of_tangent (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) :
    X * f.divXPowOrder = f := by
  simpa only [order_eq_one_of_tangent f hf hlinear, ENat.toNat_one, pow_one] using
    (X_pow_order_mul_divXPowOrder (f := f))

/-- The actual successive iterate ratios satisfy the cocycle recurrence;
it follows by cancellation of the original variable in the power-series domain. -/
theorem divXPowOrder_iterate_succ (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) (n : ℕ) :
    (powerSeriesIterate f (n + 1)).divXPowOrder =
      f.divXPowOrder * ((powerSeriesIterate f n).divXPowOrder.subst f) := by
  have hs n : (powerSeriesIterate f n).coeff 1 = 1 := by
    rw [(powerSeriesIterate_spec f hf n).2, hlinear, one_pow]
  apply mul_left_cancel₀ (X_ne_zero : (X : PowerSeries (ZMod p)) ≠ 0)
  rw [X_mul_divXPowOrder_of_tangent _ (powerSeriesIterate_spec f hf (n + 1)).1 (hs _),
    powerSeriesIterate_succ]
  calc
    (powerSeriesIterate f n).subst f = (X * (powerSeriesIterate f n).divXPowOrder).subst f := by
      rw [X_mul_divXPowOrder_of_tangent _ (powerSeriesIterate_spec f hf n).1 (hs n)]
    _ = f * ((powerSeriesIterate f n).divXPowOrder.subst f) := by
      rw [subst_mul (HasSubst.of_constantCoeff_zero' hf),
        subst_X (HasSubst.of_constantCoeff_zero' hf)]
    _ = X * (f.divXPowOrder * ((powerSeriesIterate f n).divXPowOrder.subst f)) := by
      rw [← mul_assoc, X_mul_divXPowOrder_of_tangent f hf hlinear]

private theorem principalUnitPow_congr_base (z w : PowerSeries (ZMod p))
    (hz : z.constantCoeff = 1) (hw : w.constantCoeff = 1) (h : z = w)
    (m : PadicInt p) : principalUnitPow z hz m = principalUnitPow w hw m := by
  subst w
  rfl

/-- Iterating the actual unit identity produces the actual ratio cocycle
at every original power-series iterate, without an assumed iterate formula. -/
theorem principalUnitPow_mul_subst_iterate_eq (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (U : PowerSeries (ZMod p)) (m : PadicInt p)
    (hidentity : principalUnitPow f.divXPowOrder
        (constantCoeff_divXPowOrder_of_tangent f hf hlinear) m * (U.subst f) = U)
    (n : ℕ) :
    principalUnitPow (powerSeriesIterate f n).divXPowOrder
        (constantCoeff_divXPowOrder_of_tangent _ (powerSeriesIterate_spec f hf n).1
          (by rw [(powerSeriesIterate_spec f hf n).2, hlinear, one_pow])) m *
      (U.subst (powerSeriesIterate f n)) = U := by
  induction n with
  | zero =>
    have heq := principalUnitPow_congr_base X.divXPowOrder 1
      (constantCoeff_divXPowOrder_of_tangent X (by simp) (by simp)) (by simp)
      divXPowOrder_X m
    simp only [powerSeriesIterate_zero, heq, principalUnitPow_one_base, one_mul, X_subst]
  | succ n ih =>
    have hpow := congrArg (fun V : PowerSeries (ZMod p) ↦ V.subst f) ih
    rw [subst_mul (HasSubst.of_constantCoeff_zero' hf), principalUnitPow_subst _ f _ hf m,
      subst_comp_subst_apply
        (HasSubst.of_constantCoeff_zero' (powerSeriesIterate_spec f hf n).1)
        (HasSubst.of_constantCoeff_zero' hf), ← powerSeriesIterate_succ] at hpow
    have hcs : ((powerSeriesIterate f n).divXPowOrder.subst f).constantCoeff = 1 := by
      rw [constantCoeff_subst_of_constantCoeff_zero hf]
      exact constantCoeff_divXPowOrder_of_tangent _ (powerSeriesIterate_spec f hf n).1
        (by rw [(powerSeriesIterate_spec f hf n).2, hlinear, one_pow])
    have hq := principalUnitPow_congr_base _ _
      (constantCoeff_divXPowOrder_of_tangent _ (powerSeriesIterate_spec f hf (n + 1)).1
        (by rw [(powerSeriesIterate_spec f hf (n + 1)).2, hlinear, one_pow]))
      (by
        rw [map_mul, constantCoeff_divXPowOrder_of_tangent f hf hlinear, one_mul]
        exact hcs)
      (divXPowOrder_iterate_succ f hf hlinear n) m
    rw [hq, principalUnitPow_mul_base _ _ _ hcs]
    calc
      _ = principalUnitPow f.divXPowOrder
          (constantCoeff_divXPowOrder_of_tangent f hf hlinear) m * (U.subst f) := by
        rw [mul_assoc, hpow]
      _ = U := hidentity

private theorem order_ofPowerSeries_eq (z : PowerSeries (ZMod p)) :
    (HahnSeries.ofPowerSeries ℤ (ZMod p) z).order = (z.order.toNat : ℤ) := by
  by_cases hz : z = 0
  · simp [hz]
  have he : HahnSeries.ofPowerSeries ℤ (ZMod p) z ≠ 0 := by
    intro h
    apply hz
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_zero] using h
  apply WithTop.coe_injective
  rw [HahnSeries.order_eq_orderTop_of_ne_zero he, HahnSeries.orderTop_ofPowerSeries,
    ← coe_toNat_order hz]
  rfl

/-- A unit p-adic exponent followed by an actual prime power has the exact
scaled Laurent order, including zero difference on both sides. -/
theorem order_principalUnitPow_mul_primePow_sub_one (z : PowerSeries (ZMod p))
    (hz : z.constantCoeff = 1) (u : (PadicInt p)ˣ) (r : ℕ) :
    (HahnSeries.ofPowerSeries ℤ (ZMod p)
      (principalUnitPow z hz ((u : PadicInt p) * (p : PadicInt p) ^ r) - 1)).order =
      (p ^ r : ℕ) • (HahnSeries.ofPowerSeries ℤ (ZMod p) (z - 1)).order := by
  rw [← Nat.cast_pow, principalUnitPow_mul_natCast, order_ofPowerSeries_eq,
    order_pow_prime_pow_sub_one, order_principalUnitPow_sub_one_of_isUnit z hz _ u.isUnit,
    order_ofPowerSeries_eq]
  simp only [nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_natCast,
    Nat.cast_mul]

/-- The same difference is nonzero whenever the original principal unit differs
from one. This finiteness is proved before using ordinary Laurent orders. -/
theorem principalUnitPow_mul_primePow_sub_one_ne_zero (z : PowerSeries (ZMod p))
    (hz : z.constantCoeff = 1) (u : (PadicInt p)ˣ) (r : ℕ) (hne : z ≠ 1) :
    principalUnitPow z hz ((u : PadicInt p) * (p : PadicInt p) ^ r) - 1 ≠ 0 := by
  have hbase : principalUnitPow z hz (u : PadicInt p) - 1 ≠ 0 := by
    intro heq
    have ho := order_principalUnitPow_sub_one_of_isUnit z hz _ u.isUnit
    rw [heq, order_zero] at ho
    exact hne (sub_eq_zero.mp (order_eq_top.mp ho.symm))
  rw [← Nat.cast_pow, principalUnitPow_mul_natCast, pow_prime_pow_sub_one]
  exact pow_ne_zero _ hbase

/-- The actual characteristic-p derivative kernel restricts to actual
power-series units; its Frobenius root has no negative Laurent support. -/
theorem exists_unit_pow_eq_of_derivative_eq_zero (U : PowerSeries (ZMod p))
    (hU : IsUnit U) (hD : derivative U = 0) :
    ∃ V : PowerSeries (ZMod p), IsUnit V ∧ V ^ p = U := by
  let e := HahnSeries.ofPowerSeries ℤ (ZMod p)
  have he : e U ≠ 0 := by
    intro h
    apply hU.ne_zero
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_zero] using h
  have hD' : LaurentSeries.derivative (ZMod p) (e U) = 0 := by
    rw [LaurentSeries.derivative_ofPowerSeries, hD, map_zero]
  obtain ⟨B, hB⟩ := (LaurentSeries.derivative_eq_zero_iff_exists_pow p (e U)).mp hD'
  have hBne : B ≠ 0 := by rintro rfl; simp [(Fact.out : p.Prime).ne_zero] at hB; exact he hB.symm
  have hUorder : (e U).order = 0 := by
    rw [order_ofPowerSeries_eq, order_zero_of_isUnit hU, ENat.toNat_zero, Int.natCast_zero]
  have hBo : B.order = 0 := by
    have ho := congrArg HahnSeries.order hB
    rw [HahnSeries.order_pow, hUorder, nsmul_eq_mul] at ho
    exact (mul_eq_zero.mp ho).resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hB0 : B ∈ orderAddSubgroup 0 := by
    simpa only [hBo] using mem_orderAddSubgroup_order B
  let V := mk (fun n : ℕ ↦ B.coeff n)
  have hV : e V = B := ofPowerSeries_mk_coeff_of_mem_orderAddSubgroup_zero B hB0
  have hp : V ^ p = U := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_pow, hV, hB]
  refine ⟨V, ?_, hp⟩
  exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp (hp.symm ▸ hU)

/-- Removing the original variable lowers the finite displacement order by one. -/
theorem order_divXPowOrder_sub_one_of_tangent (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) (hne : f ≠ X) :
    (HahnSeries.ofPowerSeries ℤ (ZMod p) (f.divXPowOrder - 1)).order =
      (HahnSeries.ofPowerSeries ℤ (ZMod p) f - HahnSeries.single (1 : ℤ) 1).order - 1 := by
  have hprod : X * (f.divXPowOrder - 1) = f - X := by
    rw [mul_sub, X_mul_divXPowOrder_of_tangent f hf hlinear, mul_one]
  have hq : f.divXPowOrder - 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact hne (sub_eq_zero.mp hprod.symm)
  have heq : HahnSeries.ofPowerSeries ℤ (ZMod p) (f.divXPowOrder - 1) ≠ 0 := by
    intro h
    apply hq
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_zero] using h
  have hh := congrArg (HahnSeries.ofPowerSeries ℤ (ZMod p)) hprod
  rw [map_mul, map_sub (HahnSeries.ofPowerSeries ℤ (ZMod p)) f X,
    HahnSeries.ofPowerSeries_X] at hh
  have ho := congrArg HahnSeries.order hh
  rw [HahnSeries.order_mul (by simp) heq, HahnSeries.order_single (by simp)] at ho
  omega

/-- The unit identity determines the exact finite order of its actual
substitution difference. The proof retains the nonzero statement explicitly. -/
theorem order_subst_sub_of_principalUnit_identity (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) (hne : f ≠ X)
    (U : PowerSeries (ZMod p)) (hU : IsUnit U) (u : (PadicInt p)ˣ) (r : ℕ)
    (hidentity : principalUnitPow f.divXPowOrder
      (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
      ((u : PadicInt p) * (p : PadicInt p) ^ r) * (U.subst f) = U) :
    let B := HahnSeries.ofPowerSeries ℤ (ZMod p) (U.subst f - U)
    B ≠ 0 ∧ B.order = (p ^ r : ℕ) •
      ((HahnSeries.ofPowerSeries ℤ (ZMod p) f - HahnSeries.single (1 : ℤ) 1).order - 1) := by
  let e := HahnSeries.ofPowerSeries ℤ (ZMod p)
  let P := principalUnitPow f.divXPowOrder
    (constantCoeff_divXPowOrder_of_tangent f hf hlinear) ((u : PadicInt p) * (p : PadicInt p) ^ r)
  have hq : f.divXPowOrder ≠ 1 := by
    intro h
    have he := X_mul_divXPowOrder_of_tangent f hf hlinear
    rw [h, mul_one] at he
    exact hne he.symm
  have hP : P - 1 ≠ 0 := principalUnitPow_mul_primePow_sub_one_ne_zero _ _ u r hq
  have hPe : e (P - 1) ≠ 0 := by
    intro h
    apply hP
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_zero] using h
  have hUs : IsUnit (U.subst f : PowerSeries (ZMod p)) := by
    simpa only [coe_substAlgHom] using hU.map
      (substAlgHom (R := ZMod p) (HasSubst.of_constantCoeff_zero' hf))
  have hUe : e (U.subst f) ≠ 0 := (hUs.map e).ne_zero
  have hdiff : U.subst f - U = -(P - 1) * (U.subst f) := by
    change P * (U.subst f) = U at hidentity
    linear_combination hidentity
  have horder : (e (U.subst f)).order = 0 := by
    rw [order_ofPowerSeries_eq, order_zero_of_isUnit hUs, ENat.toNat_zero, Int.natCast_zero]
  change e (U.subst f - U) ≠ 0 ∧ _
  rw [hdiff, map_mul, map_neg]
  refine ⟨mul_ne_zero (neg_ne_zero.mpr hPe) hUe, ?_⟩
  rw [HahnSeries.order_mul (neg_ne_zero.mpr hPe) hUe, HahnSeries.order_neg, horder,
    add_zero, order_principalUnitPow_mul_primePow_sub_one,
    order_divXPowOrder_sub_one_of_tangent f hf hlinear hne]

/-- A unit exponent is already impossible: actual displacement starts one
degree above the exact order forced by the principal-unit identity. -/
theorem not_principalUnit_identity_of_unit_exponent (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1) (hne : f ≠ X)
    (U : PowerSeries (ZMod p)) (hU : IsUnit U) (u : (PadicInt p)ˣ) :
    principalUnitPow f.divXPowOrder (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
      (u : PadicInt p) * (U.subst f) ≠ U := by
  intro hidentity
  let e := HahnSeries.ofPowerSeries ℤ (ZMod p)
  let δ := e f - HahnSeries.single (1 : ℤ) 1
  have hδ : δ ≠ 0 := by
    intro h
    apply hne
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [e, HahnSeries.ofPowerSeries_X] using sub_eq_zero.mp h
  have hδmem : δ ∈ orderAddSubgroup 2 := by
    simpa only [δ, e, hlinear] using ofPowerSeries_sub_linear_mem_two f hf
  have hδorder : 2 ≤ δ.order := by
    change ((2 : ℤ) : WithTop ℤ) ≤ δ.orderTop at hδmem
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hδ] at hδmem
    exact WithTop.coe_le_coe.mp hδmem
  have ho := order_subst_sub_of_principalUnit_identity f hf hlinear hne U hU u 0
    (by simpa only [pow_zero, mul_one] using hidentity)
  have hb := subst_ofPowerSeries_sub_mem (e f)
    (isAdmissible_ofPowerSeries 0 f hf (by rw [hlinear]; exact isUnit_one))
    (δ.order - 1) (by omega) (by
      change ((δ.order - 1 + 1 : ℤ) : WithTop ℤ) ≤ δ.orderTop
      rw [sub_add_cancel]
      exact mem_orderAddSubgroup_order δ) U
  rw [LaurentSeries.subst_ofPowerSeries 0 IsNilpotent.zero f hf
    (by rw [hlinear]; exact isUnit_one), ← map_sub] at hb
  change (((δ.order - 1 + 1 : ℤ) : WithTop ℤ)) ≤ (e (U.subst f - U)).orderTop at hb
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ho.1, ho.2] at hb
  simp only [pow_zero, one_nsmul] at hb
  change (((δ.order - 1 + 1 : ℤ) : WithTop ℤ)) ≤ ((δ.order - 1 : ℤ) : WithTop ℤ) at hb
  have hh := WithTop.coe_le_coe.mp hb
  omega

/-- Positive prime-power exponents force the derivative of the original unit
to vanish, using the actual unbounded prime-power iterates and Taylor remainder. -/
theorem derivative_eq_zero_of_principalUnit_identity (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (U : PowerSeries (ZMod p)) (hU : IsUnit U) (u : (PadicInt p)ˣ) (r : ℕ)
    (hidentity : principalUnitPow f.divXPowOrder
      (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
      ((u : PadicInt p) * (p : PadicInt p) ^ (r + 1)) * (U.subst f) = U) :
    derivative U = 0 := by
  by_contra hD
  let e := HahnSeries.ofPowerSeries ℤ (ZMod p)
  let D := e (derivative U)
  have hDe : D ≠ 0 := by
    intro h
    apply hD
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa only [map_zero] using h
  have ht := tendsto_primePowerIterate_ramification_atTop p f hf hlinear hinfinite
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.1 ht (D.order + 2)).exists
  let g := powerSeriesIterate f (p ^ n)
  let δ := e g - HahnSeries.single (1 : ℤ) 1
  let d := δ.order - 1
  change D.order + 2 ≤ d at hn
  have hg0 : g.constantCoeff = 0 := (powerSeriesIterate_spec f hf _).1
  have hg1 : g.coeff 1 = 1 := by
    rw [(powerSeriesIterate_spec f hf _).2, hlinear, one_pow]
  have hgn : g ≠ X := powerSeriesIterate_ne_X_of_infiniteOrder f hf _ hinfinite _
    (pow_pos (Fact.out : p.Prime).pos n)
  have hδn : δ ≠ 0 := powerSeriesIterate_displacement_ne_zero f hf _ hinfinite _
    (pow_pos (Fact.out : p.Prime).pos n)
  have hd : 1 ≤ d := by
    have := two_le_order_powerSeriesIterate_displacement f hf hlinear hinfinite _
      (pow_pos (Fact.out : p.Prime).pos n)
    change 2 ≤ δ.order at this
    omega
  have hδtop : δ.orderTop = ((d + 1 : ℤ) : WithTop ℤ) := by
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hδn]
    congr 1
    dsimp [d]
    omega
  have hi := principalUnitPow_mul_subst_iterate_eq f hf hlinear U
    ((u : PadicInt p) * (p : PadicInt p) ^ (r + 1)) hidentity (p ^ n)
  have ho := order_subst_sub_of_principalUnit_identity g hg0 hg1 hgn U hU u (r + 1) hi
  have hT := order_subst_ofPowerSeries_sub_eq (e g)
    (isAdmissible_ofPowerSeries 0 g hg0 (by rw [hg1]; exact isUnit_one))
    d hd hδtop U hDe (by change D.order < d + 1; omega)
  rw [LaurentSeries.subst_ofPowerSeries 0 IsNilpotent.zero g hg0
    (by rw [hg1]; exact isUnit_one), ← map_sub, ho.2] at hT
  change (p ^ (r + 1) : ℕ) • d = d + 1 + D.order at hT
  rw [nsmul_eq_mul] at hT
  have hpp : 2 ≤ p ^ (r + 1) := by
    have hp := (Fact.out : p.Prime).two_le
    have hpow := pow_pos (Fact.out : p.Prime).pos r
    rw [pow_succ]
    nlinarith
  have hppz : (2 : ℤ) ≤ (p ^ (r + 1) : ℕ) := by exact_mod_cast hpp
  nlinarith

/-- Frobenius descent excludes the actual identity for every exponent of the
form `unit * p^r`; the cocycle and growth are producers, not hypotheses. -/
theorem not_principalUnit_identity_of_unit_mul_primePow (f : PowerSeries (ZMod p))
    (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (u : (PadicInt p)ˣ) (r : ℕ) (U : PowerSeries (ZMod p)) (hU : IsUnit U) :
    principalUnitPow f.divXPowOrder (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
      ((u : PadicInt p) * (p : PadicInt p) ^ r) * (U.subst f) ≠ U := by
  have hfne : f ≠ X := by
    have hn := powerSeriesIterate_ne_X_of_infiniteOrder f hf _ hinfinite 1 (by omega)
    simpa only [powerSeriesIterate, Function.iterate_one,
      subst_X (HasSubst.of_constantCoeff_zero' hf)] using hn
  induction r generalizing U with
  | zero => simpa only [pow_zero, mul_one] using
      not_principalUnit_identity_of_unit_exponent f hf hlinear hfne U hU u
  | succ r ih =>
    intro hidentity
    have hD := derivative_eq_zero_of_principalUnit_identity f hf hlinear hinfinite U hU u r hidentity
    obtain ⟨V, hV, hp⟩ := exists_unit_pow_eq_of_derivative_eq_zero U hU hD
    have hpow : (principalUnitPow f.divXPowOrder
        (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
        ((u : PadicInt p) * (p : PadicInt p) ^ r) * (V.subst f)) ^ p = V ^ p := by
      calc
        _ = principalUnitPow f.divXPowOrder
            (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
            (((u : PadicInt p) * (p : PadicInt p) ^ r) * (p : PadicInt p)) *
            ((V ^ p).subst f) := by
          rw [mul_pow, principalUnitPow_mul_natCast,
            subst_pow (HasSubst.of_constantCoeff_zero' hf)]
        _ = U := by simpa only [hp, pow_succ, mul_assoc] using hidentity
        _ = V ^ p := hp.symm
    have : CharP (PowerSeries (ZMod p)) p := charP_of_injective_ringHom C_injective p
    have hroot : principalUnitPow f.divXPowOrder
        (constantCoeff_divXPowOrder_of_tangent f hf hlinear)
        ((u : PadicInt p) * (p : PadicInt p) ^ r) * (V.subst f) = V :=
      frobenius_inj (PowerSeries (ZMod p)) p hpow
    exact ih V hV hroot

/-- **Rigidity of the actual unit identity** (Yuan, proof of Lemma 4.1).
For an infinite-order substitution tangent to the identity over the prime
field, the original p-adic exponent must vanish. This includes `p = 2`. -/
theorem principalUnitPow_mul_subst_eq_implies_exponent_eq_zero
    (f : PowerSeries (ZMod p)) (hf : f.constantCoeff = 0) (hlinear : f.coeff 1 = 1)
    (hinfinite : ¬ IsOfFinOrder (powerSeriesSubstEquiv 0 IsNilpotent.zero f hf
      (by rw [hlinear]; exact isUnit_one)))
    (U : PowerSeries (ZMod p)) (hU : IsUnit U) (m : PadicInt p)
    (hidentity : principalUnitPow f.divXPowOrder
      (constantCoeff_divXPowOrder_of_tangent f hf hlinear) m * (U.subst f) = U) : m = 0 := by
  by_contra hm
  have hu := PadicInt.unitCoeff_spec hm
  exact not_principalUnit_identity_of_unit_mul_primePow f hf hlinear hinfinite
    (PadicInt.unitCoeff hm) m.valuation U hU (by simpa only [← hu] using hidentity)

end PowerSeries
