import Lemma.List.EqLengthSlice_Mul
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.GetIndices.eq.AddMul
import sympy.vector.vector
open List Nat Vector


@[main]
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


@[main]
private lemma fin
-- given
  (v : List.Vector α (m * n))
  (i : Fin m)
  (j : Fin n) :
-- imply
  (v.getSlice ⟨j, m * n, n⟩).get ⟨i, by simp [EqLengthSlice_Mul]⟩ = v.get ⟨i * n + j, AddMul.lt.Mul i j⟩ :=
-- proof
  main v i j


-- created on 2025-11-14
