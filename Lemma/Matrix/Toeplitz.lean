import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Toeplitz
open MetaMathlibExt


/--
[isToeplitzMatrix_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
private lemma isToeplitzMatrix_of_witness_eq
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : ℤ → ℝ}
-- given
  (h : ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))) :
-- imply
  IsToeplitzMatrix A := by
-- proof
  apply MetaMathlibExt.isToeplitzMatrix_of_witness h

/--
[isSymmetricToeplitzMatrix_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
private lemma isSymmetricToeplitzMatrix_of_witness_eq
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : ℤ → ℝ}
-- given
  (hsym : ∀ k : ℤ, c (-k) = c k)
  (h : ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))) :
-- imply
  IsSymmetricToeplitzMatrix A := by
-- proof
  apply MetaMathlibExt.isSymmetricToeplitzMatrix_of_witness hsym h

/--
[IsSymmetricToeplitzMatrix.isToeplitz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
private lemma IsSymmetricToeplitzMatrix_isToeplitz_eq
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
-- given
  (h : IsSymmetricToeplitzMatrix A) :
-- imply
  IsToeplitzMatrix A := by
-- proof
  apply MetaMathlibExt.IsSymmetricToeplitzMatrix.isToeplitz h

/--
[IsSymmetricToeplitzMatrix.entry_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
private lemma IsSymmetricToeplitzMatrix_entry_comm_eq
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {i j : Fin (n + 1)}
-- given
  (h : IsSymmetricToeplitzMatrix A) :
-- imply
  A i j = A j i := by
-- proof
  apply MetaMathlibExt.IsSymmetricToeplitzMatrix.entry_comm h i j


-- created on 2026-10-20
