import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.ConsLengthSlice.eq.List
import Lemma.Tensor.DotRotaryMatrix.eq.AddMulSAppend
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.SEq_Append
import Lemma.Tensor.SEqAppendS.of.SEq.SEq
import sympy.tensor.functions
open Bool List Tensor
set_option maxHeartbeats 600000


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (x : Tensor ℝ [d + d]) :
-- imply
  let x0 := cast (congrArg (Tensor ℝ) (ConsLengthSlice.eq.List.head d)) x[:d]
  let x1 := cast (congrArg (Tensor ℝ) (ConsLengthSlice.eq.List.tail d)) x[d:]
  θ.rotaryMatrix @ x = x * (θ ++ θ).cos + (-x1 ++ x0) * (θ ++ θ).sin := by
-- proof
  intro x0 x1
  have hx : x = x0 ++ x1 := by
    apply Eq.of.SEq
    apply (SEq_Append x ⟨d, by omega⟩).trans
    apply SEqAppendS.of.SEq.SEq
    ·
      apply SEq.trans (b := x[:d])
      ·
        apply SEq.of.Eq
        rfl
      ·
        apply SEq_Cast.of.Eq (ConsLengthSlice.eq.List.head d)
    ·
      apply SEq.trans (b := x[d:])
      ·
        apply SEq.of.Eq
        rfl
      ·
        apply SEq_Cast.of.Eq (ConsLengthSlice.eq.List.tail d)
  apply Eq.trans (congrArg (fun t => θ.rotaryMatrix @ t) hx)
  apply Eq.trans (DotRotaryMatrix.eq.AddMulSAppend θ x0 x1)
  rw [← hx]


-- created on 2023-06-06
-- updated on 2026-09-05
