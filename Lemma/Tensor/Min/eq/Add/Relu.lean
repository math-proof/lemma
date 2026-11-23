import Def.Data.Tensor.Relu
import Mathlib.Basic.Real.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  min x y = y - relu (-x + y) := by
-- proof
  unfold relu
  obtain h | h := le_total x y
  ·
    rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  ·
    rw [min_eq_right h, max_eq_right (by linarith)]
    ring


-- created on 2020-12-29
