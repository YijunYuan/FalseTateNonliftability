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

A ring with `p` elements, `p` prime, has characteristic `p`. This is the `Nat.card` version of
`charP_of_card_eq_prime`, which needs a `Fintype` instance.

## Main results

* `charP_of_natCard_eq_prime`: if `Nat.card R = p` is prime, then `CharP R p`.
-/

@[expose] public section

/-- A ring with `p` elements, `p` prime, has characteristic `p`. -/
theorem charP_of_natCard_eq_prime {R : Type*} [NonAssocRing R] {p : ℕ} [Fact p.Prime]
    (hR : Nat.card R = p) : CharP R p := by
  have : Finite R := Nat.finite_of_card_ne_zero (hR ▸ (Fact.out : p.Prime).ne_zero)
  have := Fintype.ofFinite R
  exact charP_of_card_eq_prime (Nat.card_eq_fintype_card.symm.trans hR)
