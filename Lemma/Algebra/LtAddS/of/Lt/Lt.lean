import Lemma.Algebra.LtAddS.is.Lt
import Lemma.Algebra.Lt.of.Lt.Lt
open Algebra


/--
Given elements `a`, `b`, `x`, and `y` in a preordered additive structure where addition is strictly monotonic on both sides, this lemma proves that if `a < b` and `x < y`, then `a + x < b + y`.
The proof leverages the strict monotonicity properties of addition to preserve the inequalities through left and right additions, then applies transitivity of the order to combine the intermediate results.
-/
@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b x y : α}
-- given
  (h₀ : a < b)
  (h₁ : x < y) :
-- imply
  a + x < b + y := by
-- proof
  have h₂ := LtAddS.of.Lt x h₀
  have h₃ := LtAddS.of.Lt.left b h₁
  apply Lt.of.Lt.Lt h₂ h₃


-- created on 2024-11-25
-- updated on 2025-04-04
