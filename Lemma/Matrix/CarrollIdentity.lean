import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.CarrollIdentity
open Matrix
open MetaMathlibExt.CarrollIdentity


/--
[carroll_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean)
-/
@[path]
private lemma carroll_identity_eq
  [CommRing R]
  {n : ℕ}
  {C : Matrix (Fin (n + 2)) (Fin (n + 2)) R}
  {i j : Fin (n + 2)}
-- given
  (hij : i ≠ j) :
-- imply
  Matrix.det C * Matrix.det (Matrix.submatrix C
    (Subtype.val : {k : Fin (n + 2) // k ≠ i ∧ k ≠ j} → Fin (n + 2))
    (Subtype.val : {k : Fin (n + 2) // k ≠ i ∧ k ≠ j} → Fin (n + 2))) =
    Matrix.det (Matrix.submatrix C (Fin.succAbove i) (Fin.succAbove i)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove j) (Fin.succAbove j)) -
    Matrix.det (Matrix.submatrix C (Fin.succAbove i) (Fin.succAbove j)) *
    Matrix.det (Matrix.submatrix C (Fin.succAbove j) (Fin.succAbove i)) := by
-- proof
  apply MetaMathlibExt.CarrollIdentity.carroll_identity n R C i j hij


-- created on 2026-10-20
