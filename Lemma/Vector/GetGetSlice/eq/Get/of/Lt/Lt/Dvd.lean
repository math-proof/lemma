import Lemma.List.EqLengthSlice_Mul
import Lemma.List.LengthSlice.eq.Div.of.Lt.Dvd
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.Any_Eq_Mul.of.Dvd
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Vector.GetGetSlice.eq.Get
open List Nat Vector


@[main]
private lemma main
-- given
  (h_d : d ∣ n)
  (h_i : i < n / d)
  (h_j : j < d)
  (v : List.Vector α n):
-- imply
  v[j : n:d].get ⟨i, by simp_all [LengthSlice.eq.Div.of.Lt.Dvd]⟩ = v.get ⟨i * d + j, LtAddMul.of.Lt.Lt_Div.Dvd h_d h_i h_j⟩ := by
-- proof
  let ⟨m, h_n⟩ := Any_Eq_Mul.of.Dvd.left h_d
  subst h_n
  rw [EqDivMul.of.Ne_0 (by omega)] at h_i
  have := GetGetSlice.eq.Get v ⟨i, h_i⟩ ⟨j, h_j⟩
  aesop


-- created on 2025-11-14
