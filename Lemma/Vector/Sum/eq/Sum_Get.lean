import Def.Data.Vector.Basic
import Instance.Data.Vector.Vector
import Lemma.List.Sum.eq.SumFinLength_Get
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Sum.eq.Sum_Get |
| fin | Vector.Sum.eq.Sum_Get.fin |
-/
@[path, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (v : List.Vector α n) :
-- imply
  v.sum = ∑ i : Fin n, v[i] := by
-- proof
  obtain ⟨v, h⟩ := v
  unfold List.Vector.sum
  simp
  rw [Sum.eq.SumFinLength_Get v]
  congr
  aesop


-- created on 2019-11-10
-- updated on 2026-11-20
