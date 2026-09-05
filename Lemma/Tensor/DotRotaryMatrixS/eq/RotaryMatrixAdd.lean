import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Int.EqNegNeg
import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
open Int Tensor


@[main]
private lemma main
-- given
  (α β : Tensor ℝ [d]) :
-- imply
  α.rotaryMatrix @ β.rotaryMatrix = (α + β).rotaryMatrix := by
-- proof
  rw [add_comm α β, Add.eq.Sub_Neg]
  apply Eq.trans (congrArg (fun t => t @ β.rotaryMatrix) (congrArg rotaryMatrix (EqNegNeg (x := α)).symm))
  rw [RotaryMatrixNeg.eq.TRotaryMatrix]
  apply DotT.eq.RotaryMatrixSub


-- created on 2026-09-03
-- updated on 2026-09-05
