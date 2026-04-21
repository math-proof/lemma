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


@[main, fin]
private lemma length_slice
-- given
  (v : List.Vector α (m * n))
  (j : Fin n)
  (i : Fin ((⟨↑↑j, ↑m * ↑n, ↑n⟩ : Slice).length (m * n))) :
-- imply
  have h_i : i < m := by
    have h_i := i.isLt
    simp [EqLengthSlice_Mul.of.Lt] at h_i
    assumption
  have h_ij := AddMul.lt.Mul.of.Lt.Lt h_i j.isLt
  v[j : m * n:n][i] = v[i * n + j] := by
-- proof
  intro h_i h_ij
  have := main v ⟨i, h_i⟩ j
  aesop


@[main, fin]
private lemma length_slice.one
-- given
  (v : List.Vector α (m * 1))
  (i : Fin ((⟨0, ↑m * 1, 1⟩ : Slice).length (m * 1))) :
-- imply
  have h_i : i < m := by
    have h_i := i.isLt
    simp [LengthSlice.eq.Min] at h_i
    assumption
  v[0 : m * 1:1][i] = v[i]'(by simpa) := by
-- proof
  intro h_i
  have := length_slice v ⟨0, by grind⟩ i (n := 1)
  aesop


@[main, fin]
private lemma one
-- given
  (v : List.Vector α (m * 1))
  (i : Fin m) :
-- imply
  v[0 : m * 1:1][i]'(by simp [LengthSlice.eq.Min]) = v[i]'(by simp) := by
-- proof
  have := main v i ⟨0, by grind⟩ (n := 1)
  aesop


-- created on 2025-11-14
