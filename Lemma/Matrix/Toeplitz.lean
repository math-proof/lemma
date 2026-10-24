import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Toeplitz
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isToeplitzMatrix_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
lemma isToeplitzMatrix_of_witness
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : ℤ → ℝ}
-- given
  (h : ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))) :
-- imply
  IsToeplitzMatrix A :=
-- proof
  ⟨c, h⟩

end MetaMathlibExt

/--
[isSymmetricToeplitzMatrix_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
lemma isSymmetricToeplitzMatrix_of_witness
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {c : ℤ → ℝ}
-- given
  (hsym : ∀ k : ℤ, c (-k) = c k)
  (h : ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))) :
-- imply
  IsSymmetricToeplitzMatrix A :=
-- proof
  ⟨c, hsym, h⟩


namespace MetaMathlibExt

/--
[IsSymmetricToeplitzMatrix.isToeplitz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
lemma IsSymmetricToeplitzMatrix.isToeplitz
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
-- given
  (h : IsSymmetricToeplitzMatrix A) :
-- imply
  IsToeplitzMatrix A := by
-- proof
  obtain ⟨c, _, hr⟩ := h
  exact ⟨c, hr⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsSymmetricToeplitzMatrix.entry_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean)
-/
@[path]
lemma IsSymmetricToeplitzMatrix.entry_comm
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {i j : Fin (n + 1)}
-- given
  (h : IsSymmetricToeplitzMatrix A) :
-- imply
  A i j = A j i := by
-- proof
  obtain ⟨c, hsym, hr⟩ := h
  have hdiff : (i.val : ℤ) - (j.val : ℤ) = -((j.val : ℤ) - (i.val : ℤ)) := by
    omega
  rw [hr i j, hr j i, hdiff, hsym]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
