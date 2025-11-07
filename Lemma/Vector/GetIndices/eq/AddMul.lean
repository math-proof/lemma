import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Nat.LtVal
import Lemma.Vector.EqLengthSlice.of.Lt
import sympy.vector.vector
open Nat Vector


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  (List.Vector.indices ⟨j, m * n, n⟩ (m * n)).get ⟨i, by simp [EqLengthSlice.of.Lt m (LtVal j)]⟩ = ↑i * n + j := by
-- proof
  unfold List.Vector.indices Slice.toList
  simp
  split_ifs with h
  ·
    sorry
  ·
    sorry


-- created on 2025-11-07
