import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Nat.EqMod
open Vector Nat


@[main, fin]
private lemma main
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector α n) :
-- imply
  (v.repeat m)[t]'(by convert AddMul.lt.Mul i j) = v[j] := by
-- proof
  simp [GetElem.getElem]
  simp [GetRepeat.eq.Get_Mod.fin]
  simp [h_t]
  simp [EqMod]


-- created on 2025-09-24
