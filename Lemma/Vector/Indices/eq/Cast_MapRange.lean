import Lemma.Bool.EqCast.of.SEq
import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.Indices.as.MapRange
open Vector List Bool Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (j : Fin n)
  (m : ℕ) :
-- imply
  List.Vector.indices ⟨j, m * n, n⟩ (m * n) = cast (by rw [EqLengthSlice_Mul.of.Lt j.isLt]) ((List.Vector.range m).map fun i : Fin m => (⟨↑i * n + j, AddMul.lt.Mul i j⟩ : Fin (m * n))) := by
-- proof
  apply Eq_Cast.of.SEq
  apply Indices.as.MapRange


@[main]
private lemma comm'
  {n : ℕ}
-- given
  (j : Fin n)
  (m : ℕ) :
-- imply
   List.Vector.indices ⟨j, n * m, n⟩ (n * m) = cast (by rw [EqLengthSlice_Mul.of.Lt.comm j.isLt]) ((List.Vector.range m).map fun i : Fin m => (⟨↑i * n + j, AddMul.lt.Mul.comm i j⟩ : Fin (n * m))) := by
-- proof
  apply Eq_Cast.of.SEq
  apply Indices.as.MapRange.comm


-- created on 2025-11-10
