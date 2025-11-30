import Lemma.Real.ExpAdd.eq.MulExpS
import Lemma.Vector.GetAdd.eq.AddGet
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.MulGetS
open Real Vector


@[main]
private lemma main
  [Exp α]
-- given
  (a b : List.Vector α n) :
-- imply
  exp (a + b) = exp a * exp b := by
-- proof
  ext i
  rw [GetExp.eq.ExpGet.fin]
  rw [GetAdd.eq.AddGetS.fin]
  rw [GetMul.eq.MulGetS.fin]
  simp [GetExp.eq.ExpGet.fin]
  rw [ExpAdd.eq.MulExpS]


@[main]
private lemma scalar
  [Exp α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  exp (x + a) = exp x * exp a := by
-- proof
  ext i
  rw [GetExp.eq.ExpGet.fin]
  rw [GetAdd.eq.AddGet.fin]
  rw [GetMul.eq.MulGet.fin]
  simp [GetExp.eq.ExpGet.fin]
  rw [@Real.ExpAdd.eq.MulExpS]


-- created on 2025-11-30
