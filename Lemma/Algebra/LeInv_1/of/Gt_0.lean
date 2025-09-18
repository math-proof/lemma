import Lemma.Algebra.LeInvS.of.Ge.Gt_0
import Lemma.Algebra.Ge_Add_1.of.Gt
open Algebra


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  (n : ℝ)⁻¹ ≤ 1 := by
-- proof
  have : (n : ℝ) ≥ 1 := by
    have := Ge_Add_1.of.Gt h
    norm_num at this
    norm_cast
  have := LeInvS.of.Ge.Gt_0 (by norm_num : (1 : ℝ) > 0) this
  norm_num at this
  assumption


-- created on 2025-03-02
-- updated on 2025-03-04
