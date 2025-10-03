import sympy.vector.vector
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Vector.Eq.of.EqValS
open Logic Vector


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h : a.val = b.val) :
-- imply
  HEq a b := by
-- proof
  have h_length := EqUFnS.of.Eq h (·.length)
  simp at h_length
  let b' : List.Vector α n := cast (by rw [h_length]) b
  have h_Eq : a.val = b'.val := by
    simp [b']
    rw [h]
    congr
    rw [h_length]
    simp_all
  have h_Eq := Eq.of.EqValS h_Eq
  simp_all
  simp [b']


-- created on 2025-05-21
