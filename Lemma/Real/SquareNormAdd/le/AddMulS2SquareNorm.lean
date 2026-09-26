import Mathlib.Analysis.Normed.Group.Basic
import Lemma.Nat.SquareAdd.le.AddMulS2Square
open Nat


@[main]
private lemma main
  [SeminormedAddGroup E]
-- given
  (x y : E) :
-- imply
  ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
-- proof
  calc
    _ ≤ (‖x‖ + ‖y‖) ^ 2 := by gcongr; exact norm_add_le x y
    _ ≤ _ := SquareAdd.le.AddMulS2Square ‖x‖ ‖y‖


-- created on 2026-09-26