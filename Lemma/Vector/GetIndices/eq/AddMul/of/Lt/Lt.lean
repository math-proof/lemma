import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.Vector.GetIndices.eq.AddMul
import sympy.vector.vector
open Vector List


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h_i : i < m)
  (h_j : j < n) :
-- imply
  (List.Vector.indices ⟨j, m * n, n⟩ (m * n))[i]'(by simpa [EqLengthSlice_Mul.of.Lt h_j]) = i * n + j :=
-- proof
  GetIndices.eq.AddMul ⟨i, h_i⟩ ⟨j, h_j⟩


-- created on 2025-11-10
