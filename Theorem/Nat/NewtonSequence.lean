module

public import Mathlib
public import Def.NumberTheory.NewtonSequence

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsNewtonSequence.eq_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NewtonSequence.lean)
-/
public theorem IsNewtonSequence.eq_recurrence
  [CommSemiring R]
  {a c : ℕ → R}
  {n : ℕ}
-- given
  (h : IsNewtonSequence a c) :
-- imply
  a (n + 1) =
      (∑ j ∈ Finset.range n, a (n - j) * c (j + 1)) + ((n + 1 : ℕ) : R) * c (n + 1) :=
-- proof
  h n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
