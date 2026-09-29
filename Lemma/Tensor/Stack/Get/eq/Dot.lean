import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
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


-- created on 2026-09-27
