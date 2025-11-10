import Lemma.List.EqLengthSlice_CoeMul.of.Lt
import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.LtVal
import Lemma.Vector.EqGetRange.of.Lt
import Lemma.Vector.GetIndices.eq.AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Vector List Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (j : Fin n)
  (m : ℕ):
-- imply
  List.Vector.indices ⟨j, m * n, n⟩ (m * n) ≃ (List.Vector.range m).map fun i : Fin m => ⟨↑i * n + j, AddMul.lt.Mul i j⟩ := by
-- proof
  apply SEq.of.All_EqGetS.Eq
  ·
    intro t
    have h_t := LtVal t
    simp [EqLengthSlice_Mul.of.Lt] at h_t
    simp [EqGetRange.of.Lt]
    apply Eq_Mk.of.EqVal
    simp only [GetElem.getElem]
    rw [GetIndices.eq.AddMul ⟨t, h_t⟩ j]
  ·
    apply EqLengthSlice_CoeMul.of.Lt
    simp


@[main]
private lemma Comm
  {n : ℕ}
-- given
  (j : Fin n)
  (m : ℕ):
-- imply
  List.Vector.indices ⟨j, n * m, n⟩ (n * m) ≃ (List.Vector.range m).map fun i : Fin m => ⟨↑i * n + j, AddMul.lt.Mul.comm i j⟩ := by
-- proof
  apply SEq.of.All_EqGetS.Eq
  ·
    intro t
    have h_t := LtVal t
    simp [EqLengthSlice_Mul.of.Lt.comm] at h_t
    simp [EqGetRange.of.Lt]
    apply Eq_Mk.of.EqVal
    simp only [GetElem.getElem]
    rw [GetIndices.eq.AddMul.comm ⟨t, h_t⟩ j]
  ·
    apply EqLengthSlice_CoeMul.of.Lt.comm
    simp


-- created on 2025-11-10
