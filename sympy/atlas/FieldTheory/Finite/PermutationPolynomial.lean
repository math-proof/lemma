/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PermutationPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Permutation polynomials complete to level `k`

Source: S. Rajagopal and P. Vanchinathan, *Higher Level Completeness for
Permutation Polynomials* (arXiv `2310.12466v1`). A polynomial `f ∈ F_q[X]` is
complete to level `k` (`k`-complete) when `f` together with `f + x`, …,
`f + kx` are all permutation polynomials.
-/

namespace Polynomial

/-- A polynomial over a finite field is a permutation polynomial when its
evaluation self-map is bijective. -/
def IsPermutationPolynomial {F : Type*} [Field F] [Finite F]
    (f : Polynomial F) : Prop :=
  Function.Bijective fun x => f.eval x

/-- A polynomial `f` over a finite field is complete to level `k`
(`k`-complete) when `f + i * X` is a permutation polynomial for every natural
index `i ≤ k`, with `i` cast into `F`. The source assumes positive `k`; the
predicate is stated for all natural levels, with the positive-level
characterization `isKComplete_succ_iff` and the zero-level boundary
`isKComplete_zero` below. -/
def IsKComplete {F : Type*} [Field F] [Finite F] (f : Polynomial F)
    (k : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ k → IsPermutationPolynomial (f + Polynomial.C (i : F) * Polynomial.X)
end Polynomial
