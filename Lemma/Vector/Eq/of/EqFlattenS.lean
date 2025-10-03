import sympy.vector.vector
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.List.Eq_Nil.of.EqLength_0
import Lemma.Vector.Eq_Cons_Tail
import Lemma.Vector.ValFlattenCons.eq.ValAppend_Flatten
import Lemma.Vector.Eq.of.EqFlattenSMap.EqLengthS
open Logic Vector List


@[main]
private lemma main
  {a b : List.Vector (List.Vector α n) m}
-- given
  (h : a.flatten = b.flatten) :
-- imply
  a = b := by
-- proof
  simp [List.Vector.flatten] at h
  simp [List.Vector.toList] at h
  let ⟨a, ha_length⟩ := a
  let ⟨b, hb_length⟩ := b
  congr
  have h := EqUFnS.of.Eq h fun t => t.val
  simp at h
  have h_length : a.length = b.length := by
    aesop
  apply Eq.of.EqFlattenSMap.EqLengthS h_length h


-- created on 2025-05-11
