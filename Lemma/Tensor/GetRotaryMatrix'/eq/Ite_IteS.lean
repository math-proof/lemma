import Lemma.Tensor.EqGetStack
import Lemma.Tensor.RotaryMatrix'.eq.Stack_Ite_IteS
open Tensor


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (i j : Fin (d + d)) :
-- imply
  (rotaryMatrix' θ)[i][j] =
    if (i : ℕ) % 2 = 0 then
      if (j : ℕ) = (i : ℕ) then
        (θ.cos[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else if (j : ℕ) = (i : ℕ) + 1 then
        -(θ.sin[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else
        (0 : Tensor ℝ [])
    else
      if (j : ℕ) = (i : ℕ) then
        (θ.cos[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else if (j : ℕ) + 1 = (i : ℕ) then
        (θ.sin[(i : ℕ) / 2]'(by grind) : Tensor ℝ [])
      else
        (0 : Tensor ℝ []) := by
-- proof
  simp only [rotaryMatrix', Nat.even_iff]
  apply (congrArg (fun t => t[j]) (EqGetStack.fin _ _)).trans
  apply EqGetStack.fin


-- created on 2026-09-04
