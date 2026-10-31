import Def.LinearAlgebra.Matrix.Permutation
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma swap
  {n : ℕ}
  {w : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ}
  {i j : Fin n}
-- given
  (h : ∀ i j, w i j = swapMatrix i j) :
-- imply
  w i j = w j i := by
-- proof
  rw [h i j, h j i, swapMatrix, swapMatrix, Equiv.swap_comm]


-- created on 2020-08-25
