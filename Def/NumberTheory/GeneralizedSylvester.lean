/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedSylvester.lean -/

import Mathlib.Data.Nat.Basic
/-!
# Generalized Sylvester sequence

This file defines the generalized Sylvester sequence from
[Y. Kamio, *Asymptotic Analysis of Infinite Decompositions of a Unit Fraction into Unit
Fractions*](https://arxiv.org/abs/2503.02317v1), Definition 2.1.

The paper indexes the sequence from one. Thus `generalizedSylvester n k` is its
`s_{k + 1}(n)`. The definition is extended to every `n : ℕ`; the paper assumes `0 < n`
when proving later properties of the sequence.
-/


namespace Nat

/-- The generalized Sylvester sequence, indexed from zero.

The paper's `s₁(n)` is `generalizedSylvester n 0`.
-/
def generalizedSylvester (n : ℕ) : ℕ → ℕ
  | 0 => n + 1
  | k + 1 => generalizedSylvester n k ^ 2 - generalizedSylvester n k + 1

end Nat
