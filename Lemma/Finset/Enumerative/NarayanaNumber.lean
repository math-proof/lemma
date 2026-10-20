import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.NarayanaNumber
open MetaMathlibExt


/--
[narayana_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaNumber.lean)
-/
@[path]
private lemma narayana_eq_eq
  {n k : {n : ℕ // 0 < n}} :
-- imply
  narayana n k
      = (Nat.choose n.val k.val * Nat.choose n.val (k.val - 1)) / n.val := by
-- proof
  apply MetaMathlibExt.narayana_eq n k

/--
[narayana_eq_second](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaNumber.lean)
-/
@[path]
private lemma narayana_eq_second_eq
  {n k : {n : ℕ // 0 < n}} :
-- imply
  narayana n k
      = (Nat.choose (n.val - 1) (k.val - 1) * Nat.choose n.val (k.val - 1))
        / k.val := by
-- proof
  apply MetaMathlibExt.narayana_eq_second n k


-- created on 2026-10-20
