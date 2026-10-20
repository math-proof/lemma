import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Composite
open Nat


/--
[IsComposite.one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Composite.lean)
-/
@[path]
private lemma IsComposite_one_lt_eq
  {n : ℕ}
-- given
  (h : n.IsComposite) :
-- imply
  1 < n := by
-- proof
  apply Nat.IsComposite.one_lt h

/--
[IsComposite.not_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Composite.lean)
-/
@[path]
private lemma IsComposite_not_prime_eq
  {n : ℕ}
-- given
  (h : n.IsComposite) :
-- imply
  ¬ n.Prime := by
-- proof
  apply Nat.IsComposite.not_prime h


-- created on 2026-10-20
