import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.Order.Dilworth.Part2
open MathlibExt MathlibExt.Combinatorics MathlibExt.Combinatorics.Order MathlibExt.Combinatorics.Order.DilworthWanted


namespace MathlibExt.Combinatorics.Order.DilworthWanted

/--
[discrete3_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean)
-/
@[path]
lemma discrete3_le
  {a b : Discrete3} :
-- imply
  a ≤ b ↔ a = b :=
-- proof
  Iff.rfl

end MathlibExt.Combinatorics.Order.DilworthWanted


-- created on 2026-10-23
