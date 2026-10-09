import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetMul.eq.MulGet
open Vector


@[path]
private lemma main
  [Mul α]
-- given
  (h : n = n')
  (x : List.Vector α n)
  (a : α) :
-- imply
  have h := congrArg (List.Vector α) h
  cast h (x * a) = cast h x * a := by
-- proof
  ext i
  rw [GetMul.eq.MulGet.fin]
  simp [GetCast.eq.Get.of.Eq.fin h]
  rw [GetMul.eq.MulGet.fin]


-- created on 2025-12-01
