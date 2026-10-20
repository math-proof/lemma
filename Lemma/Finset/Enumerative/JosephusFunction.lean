import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.JosephusFunction
open MetaMathlibExt


/--
[josephus_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean)
-/
@[path]
private lemma josephus_one_eq
  {k : Nat}
-- given
  (hk : 2 ≤ k) :
-- imply
  josephus k 1 = 1 := by
-- proof
  apply MetaMathlibExt.josephus_one k hk

/--
[josephus_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean)
-/
@[path]
private lemma josephus_succ_eq
  {k n : Nat}
-- given
  (hk : 2 ≤ k)
  (hn : 1 ≤ n) :
-- imply
  josephus k (n + 1) = ((josephus k n + k - 1) % (n + 1)) + 1 := by
-- proof
  apply MetaMathlibExt.josephus_succ k n hk hn

/--
[josephus_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean)
-/
@[path]
private lemma josephus_range_eq
  {k n : Nat}
-- given
  (hk : 2 ≤ k)
  (hn : 1 ≤ n) :
-- imply
  1 ≤ josephus k n ∧ josephus k n ≤ n := by
-- proof
  apply MetaMathlibExt.josephus_range k n hk hn


-- created on 2026-10-20
