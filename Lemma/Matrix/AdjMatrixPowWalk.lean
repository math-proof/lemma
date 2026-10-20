import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.AdjMatrixPowWalk
open scoped BigOperators
open MetaMathlibExt


/--
[adjMatrix_pow_weighted_walk_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/AdjMatrixPowWalk.lean)
-/
@[path]
private lemma adjMatrix_pow_weighted_walk_sum_eq
  [CommSemiring R]
  {k : ℕ}
  {A : Matrix (Fin k) (Fin k) R}
  {n : ℕ}
  {i j : Fin k} :
-- imply
  (A ^ n) i j =
    ∑ p ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin k)))).filter
    (fun p => p 0 = i ∧ p (Fin.last n) = j),
    ∏ t : Fin n, A (p t.castSucc) (p t.succ) := by
-- proof
  apply MetaMathlibExt.adjMatrix_pow_weighted_walk_sum A n i j


-- created on 2026-10-20
