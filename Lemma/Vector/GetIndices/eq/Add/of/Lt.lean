import sympy.vector.vector
import Lemma.Vector.GetIndices.eq.Add
open Vector


@[main]
private lemma main
  {j n i : ℕ}
-- given
  (h : i < (⟨j, (n + j : ℕ), 1⟩ : Slice).length (n + j)) :
-- imply
  (List.Vector.indices ⟨j, (n + j : ℕ), 1⟩ (n + j))[i] = (i : ℕ) + j := by
-- proof
  let i : Fin _ := ⟨i, h⟩
  have := GetIndices.eq.Add j n i
  assumption


-- created on 2025-05-28
