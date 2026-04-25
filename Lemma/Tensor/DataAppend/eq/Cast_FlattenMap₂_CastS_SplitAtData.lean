import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.DataAppend.as.AppendDataS
open Bool Tensor


@[main]
private lemma main
  {b_z : List ℕ}
-- given
  (A : Tensor α (b_z ++ m :: s))
  (B : Tensor α (b_z ++ n :: s)) :
-- imply
  let a : List.Vector (List.Vector α (m * s.prod)) b_z.prod := cast (by simp) (A.data.splitAt b_z.length)
  let b : List.Vector (List.Vector α (n * s.prod)) b_z.prod := cast (by simp) (B.data.splitAt b_z.length)
  (A ++ B).data = cast (congrArg (List.Vector α) (by grind)) (List.Vector.map₂ (fun v₀ v₁=> v₀ ++ v₁) a b).flatten := by
-- proof
  apply Eq_Cast.of.SEq
  sorry


-- created on 2026-04-25
