/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FalseTateNonliftability.LaurentSeries.Evaluation
public import FalseTateNonliftability.LaurentSeries.NormalForm
public import FalseTateNonliftability.LaurentSeries.Substitution
public import FalseTateNonliftability.LaurentSeries.Taylor

/-!
# Laurent series

Substitution `f ↦ f(G)` in Laurent series over local Artinian rings with principal maximal ideal
(Yuan, Lemma 2.1), the Taylor expansion of substitutions close to the identity (Yuan, Lemma 3.2
and the proofs of Theorem 3.1 and Lemma 4.2), and ramification numbers, their growth under
`p`-th powers, and normal forms (Yuan, §3.2: Lemma 3.3 and Theorem 3.4).

## References

* Y. Yuan, *Non-liftability of the field of norms of the p-adic false Tate curve extension*,
  §2.1 and §3.
-/
