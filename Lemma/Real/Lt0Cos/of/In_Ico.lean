import Lemma.Set.Ge.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
import Lemma.Real.GtPi0
open Set Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ico 0 (π / 2)) :
-- imply
  cos x > 0 := by
-- proof
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨?_, Lt.of.In_Ico h⟩
  linarith [Ge.of.In_Ico h, GtPi0]


-- created on 2018-06-23
