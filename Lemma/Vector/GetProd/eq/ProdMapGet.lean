import Lemma.Vector.EqGet1_1
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.ProdCons.eq.Mul_Prod
open Vector


@[main, fin, val]
private lemma main
  [Mul α] [One α]
-- given
  (x : List.Vector (List.Vector α n) m)
  (i : Fin n) :
-- imply
  x.prod[i] = (x.map (·[i])).prod := by
-- proof
  induction x using List.Vector.inductionOn with
  | nil =>
    simp [List.Vector.prod]
    apply EqGet1_1
  | cons ih =>
    rw [ProdCons.eq.Mul_Prod, GetMul.eq.MulGetS, ih]
    congr 1


-- created on 2026-09-06
