import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.Basic
open Bool


@[main, cast]
private lemma main
  {b_z : List ℕ}
-- given
  (A : Tensor α (b_z ++ m :: s))
  (B : Tensor α (b_z ++ n :: s)) :
-- imply
  let a : List.Vector (List.Vector α (m * s.prod)) b_z.prod := cast (by simp) (A.data.splitAt b_z.length)
  let b : List.Vector (List.Vector α (n * s.prod)) b_z.prod := cast (by simp) (B.data.splitAt b_z.length)
  (A ++ B).data ≃ (List.Vector.map₂ HAppend.hAppend a b).flatten := by
-- proof
  apply SEq.of.Eq_Cast
  .
    simp [HAppend.hAppend]
  .
    grind


-- created on 2026-04-25
-- updated on 2026-05-02
