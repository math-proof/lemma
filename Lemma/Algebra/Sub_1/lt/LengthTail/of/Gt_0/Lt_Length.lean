import Lemma.Algebra.Ge_1.of.Gt_0
import Lemma.Algebra.Gt.of.Gt.Ge
import Lemma.Algebra.LtSubS.of.Lt.Le
open Algebra


@[main]
private lemma main
  {i : ℕ}
  {s : List α}
-- given
  (h₀ : i < s.length)
  (h₁ : i > 0) :
-- imply
  i - 1 < s.tail.length := by
-- proof
  simp
  apply LtSubS.of.Lt.Le h₁ h₀


-- created on 2025-06-22
