import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.GroupTheory.Perm.Sign
import sympy.Basic


/-- py: the determinant of a (block) permutation matrix obtained by `s` column swaps is `(-1)^s`.
Blocks are flattened to entries (index type `ι`, e.g. a Σ-type of block indices); the swaps are the
list `l` of transpositions whose product is the permutation. -/
@[main]
private lemma main
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {σ : Equiv.Perm ι}
  {l : List (Equiv.Perm ι)}
-- given
  (h₀ : ∀ g ∈ l, g.IsSwap)
  (h₁ : σ = l.prod) :
-- imply
  (σ.permMatrix ℝ).det = (-1) ^ l.length := by
-- proof
  rw [Matrix.det_permutation, h₁, Equiv.Perm.sign_prod_list_swap h₀]
  push_cast
  rfl


-- created on 2021-11-21
