import Def.LinearAlgebra.Matrix.Permutation
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Matrix


@[path]
private lemma swap
  {n : ℕ}
  {x : Fin n → ℂ}
  {i j : Fin n} :
-- imply
  (fun k => x (Equiv.swap i j k)) = swapMatrix i j *ᵥ x := by
-- proof
  funext k
  symm
  simp [swapMatrix, Matrix.mulVec, dotProduct]


-- created on 2020-08-26
