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
  simp only [swapMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine (Finset.sum_eq_single (Equiv.swap i j k) (fun e _ he => ?_) (fun h => ?_)).trans ?_
  ·
    have hne : Equiv.swap i j k ≠ e := fun hswap => he hswap.symm
    simp [KroneckerDelta, hne]
  ·
    apply absurd (Finset.mem_univ _) h
  ·
    simp [KroneckerDelta]


-- created on 2020-08-26
-- updated on 2026-11-13
