import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.YoungReverseMultiples
open MetaMathlibExt


/--
[young_reverse_multiples_equiv_pivot_paths](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultiples.lean)
-/
@[path]
private lemma young_reverse_multiples_equiv_pivot_paths_eq
  {g k : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkg : k < g) :
-- imply
  let digitValue := by
-- proof
  apply MetaMathlibExt.young_reverse_multiples_equiv_pivot_paths g k hk hkg


-- created on 2026-10-20
