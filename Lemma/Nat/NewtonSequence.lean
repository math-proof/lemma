import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NewtonSequence
open MetaMathlibExt


/--
[IsNewtonSequence.eq_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NewtonSequence.lean)
-/
@[path]
private lemma IsNewtonSequence_eq_recurrence_eq
  [CommSemiring R]
  {a c : ℕ → R}
  {n : ℕ}
-- given
  (h : IsNewtonSequence a c) :
-- imply
  a (n + 1) =
      (∑ j ∈ Finset.range n, a (n - j) * c (j + 1)) + ((n + 1 : ℕ) : R) * c (n + 1) := by
-- proof
  apply MetaMathlibExt.IsNewtonSequence.eq_recurrence h n


-- created on 2026-10-20
