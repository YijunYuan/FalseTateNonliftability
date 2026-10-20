/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Rings with a prime number of elements

A ring `R` with `p` elements, where `p` is a prime number, has characteristic `p`.

This file is a candidate for upstreaming to Mathlib, next to `charP_of_card_eq_prime` in
`Mathlib.Algebra.CharP.CharAndCard`, which states the same result for `Fintype.card`.

## Main results

* `charP_of_natCard_eq_prime`: if `Nat.card R = p` with `p` prime, then `R` has characteristic `p`.
-/

@[expose] public section

/-- A ring with `p` elements, `p` prime, has characteristic `p`. -/
theorem charP_of_natCard_eq_prime {R : Type*} [NonAssocRing R] {p : ℕ} [Fact p.Prime]
    (hR : Nat.card R = p) : CharP R p := by
  have : Finite R := Nat.finite_of_card_ne_zero (hR ▸ (Fact.out : p.Prime).ne_zero)
  have := Fintype.ofFinite R
  exact charP_of_card_eq_prime (Nat.card_eq_fintype_card.symm.trans hR)
