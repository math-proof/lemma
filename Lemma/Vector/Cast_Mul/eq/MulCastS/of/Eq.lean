import Lemma.Vector.GetCast.eq.Get.of.Eq
import Theorem.Vector.GetMul.eq.MulGetS
open Vector


@[path]
private lemma main
  [Mul α]
-- given
  (h : n = n')
  (a b : List.Vector α n) :
-- imply
  have h := congrArg (List.Vector α) h
  cast h (a * b) = cast h a * cast h b := by
-- proof
  ext i
  rw [GetMul.eq.MulGetS.fin]
  simp [GetCast.eq.Get.of.Eq.fin h]
  rw [GetMul.eq.MulGetS.fin]


-- created on 2025-12-01
-- updated on 2026-11-20
