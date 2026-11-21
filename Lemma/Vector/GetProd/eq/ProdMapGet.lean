import Theorem.Vector.EqGet1_1
import Theorem.Vector.GetMul.eq.MulGetS
import Lemma.Vector.ProdCons.eq.Mul_Prod
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetProd.eq.ProdMapGet |
| fin | Vector.GetProd.eq.ProdMapGet.fin |
| val | Vector.GetProd.eq.ProdMapGet.val |
-/
@[path, fin, val]
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
-- updated on 2026-11-20
