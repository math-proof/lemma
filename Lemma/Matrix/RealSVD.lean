import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.RealSVD
open Matrix
open MathlibExt.LinearAlgebra.Matrix.RealSVDWanted


/--
[exists_orthogonalGroup_mul_eq_rectangularDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RealSVD.lean)
-/
@[path]
private lemma exists_orthogonalGroup_mul_eq_rectangularDiagonal_eq
  {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) ℝ} :
-- imply
  ∃ (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (σ : Fin n → ℝ),
    (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
    A * (V : Matrix (Fin n) (Fin n) ℝ) =
    (U : Matrix (Fin m) (Fin m) ℝ) *
    Matrix.of (fun i j => if i.val = j.val then σ j else 0) := by
-- proof
  apply Matrix.exists_orthogonalGroup_mul_eq_rectangularDiagonal m n A

/--
[exists_orthogonalGroup_rectangularDiagonal_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RealSVD.lean)
-/
@[path]
private lemma exists_orthogonalGroup_rectangularDiagonal_antitone_eq
  {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) ℝ} :
-- imply
  ∃ (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (σ : Fin n → ℝ),
    (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
    A = (U : Matrix (Fin m) (Fin m) ℝ) *
    Matrix.of (fun i j => if i.val = j.val then σ j else 0) *
    Matrix.transpose (V : Matrix (Fin n) (Fin n) ℝ) := by
-- proof
  apply Matrix.exists_orthogonalGroup_rectangularDiagonal_antitone m n A

/--
[real_singular_value_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/RealSVD.lean)
-/
@[path]
private lemma real_singular_value_decomposition_eq
  {m n : ℕ}
  {A : Matrix (Fin m) (Fin n) ℝ} :
-- imply
  ∃ (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ),
    (∀ j, 0 ≤ σ j) ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
    U ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧ V ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
    A = U * Matrix.of (fun i j => if i.val = j.val then σ j else 0) *
    Matrix.transpose V := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.RealSVDWanted.real_singular_value_decomposition m n A


-- created on 2026-10-20
