import Lemma.Algebra.LtDivS.of.Lt.Gt_0
import Lemma.Nat.Ne.of.Gt
import Lemma.Algebra.EqDivMul.of.Ne_0
open Algebra Nat


/--
Given real numbers \( x \) and \( y \), if their product \( x \cdot y \) is negative and \( y \) is positive, then \( x \) must be negative.
This lemma leverages the properties of inequalities and division by a positive number to establish the sign of \( x \) based on the sign of the product.
-/
@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x * y < 0)
  (h₁ : y > 0) :
-- imply
  x < 0 := by
-- proof
  have h_Ne_0 := Ne.of.Gt h₁
  have := LtDivS.of.Lt.Gt_0 h₀ h₁
  rw [EqDivMul.of.Ne_0 h_Ne_0] at this
  norm_num at this
  assumption


-- created on 2025-03-24
-- updated on 2025-04-04
