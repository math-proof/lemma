import torch.nn.functional.relu
import Mathlib.Data.Real.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  relu (y - x) = y - min x y := by
-- proof
  unfold relu
  rcases le_total x y with h | h
  ·
    rw [min_eq_left h, max_eq_left (by linarith)]
  ·
    rw [min_eq_right h, max_eq_right (by linarith)]
    ring


-- created on 2021-12-15
