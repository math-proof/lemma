import Lemma.Set.Ge.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
import sympy.functions.elementary.trigonometric
import sympy.sets.sets
import sympy.Basic
open Set


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ico (0 : ℝ) (π / 2)) :
-- imply
  Real.cos x > 0 := by
-- proof
  apply Real.cos_pos_of_mem_Ioo
  refine ⟨?_, Lt.of.In_Ico h⟩
  linarith [Ge.of.In_Ico h, Real.pi_pos]


-- created on 2018-06-23
