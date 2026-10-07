import sympy.stats.step_size
import sympy.Basic
import Lemma.Real.Anchors.TimeAdd1.eq.FindExistsLe
open Finset Filter


@[main]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α}
  {n : ℕ} :
-- imply
  anc.t n < anc.t (n + 1) := by
-- proof
  rw [(Real.Anchors.TimeAdd1.eq.FindExistsLe anc) n]
  refine (Nat.lt_find_iff _ _).2 fun m hm => ?_
  simp only [Anchors.le, not_le]
  rw [Ico_eq_empty_of_le hm, sum_empty]
  exact anc.hT.pos n


-- created on 2026-09-26