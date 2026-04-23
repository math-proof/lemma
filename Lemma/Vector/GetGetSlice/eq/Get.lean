import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.List.LengthSlice.eq.Min
import Lemma.List.EqLengthSlice_Mul
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.GetIndices.eq.AddMul
import sympy.vector.vector
open List Nat Vector


@[main, fin]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (i : Fin m)
  (j : Fin n) :
-- imply
  v[j : m * n:n][i]'(by simp [EqLengthSlice_Mul]) = v[i * n + j]'(AddMul.lt.Mul i j) := by
-- proof
  unfold List.Vector.getSlice
  simp [GetElem.getElem]
  apply congrArg
  simp [List.Vector.length]
  have := GetIndices.eq.AddMul i j
  aesop


-- created on 2025-11-14
