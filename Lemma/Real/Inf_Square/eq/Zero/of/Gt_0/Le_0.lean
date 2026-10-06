import sympy.sets.sets
import sympy.Basic
import Lemma.Real.Inf_Square.eq.Zero.of.Gt_0.Lt_0
import Lemma.Real.Inf_Square.eq.Square.of.Ge_0.Lt


@[main]
private lemma main
  {m M : ℝ}
-- given
  (hM : M > 0)
  (hm : m ≤ 0) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m M) = 0 := by
-- proof
  if hmlt : m < 0 then
    exact Real.Inf_Square.eq.Zero.of.Gt_0.Lt_0 hM hmlt
  else
    have hmeq : m = 0 := by linarith
    subst hmeq
    rw [Real.Inf_Square.eq.Square.of.Ge_0.Lt le_rfl hM]
    norm_num


-- created on 2019-08-25
-- updated on 2023-05-20
