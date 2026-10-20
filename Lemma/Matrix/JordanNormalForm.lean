import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.JordanNormalForm
open Module
open scoped BigOperators
open MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
open LinearMap
open Module.End


/--
[jordanBlock_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean)
-/
@[path]
private lemma jordanBlock_apply_eq
  [Field K]
  {s : ℕ}
  {μ : K}
  {i j : Fin s} :
-- imply
  jordanBlock s μ i j = (if i.val + 1 = j.val then 1 else if i = j then μ else 0) := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted.jordanBlock_apply s μ i j

/--
[toMatrix_eq_jordanBlock](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean)
-/
@[path]
private lemma toMatrix_eq_jordanBlock_eq
  [Field K] [AddCommGroup V] [Module K V]
  {d : ℕ}
  {b : Basis (Fin (d + 1)) K V}
  {f : Module.End K V}
  {μ : K}
-- given
  (hzero : f (b 0) = μ • b 0)
  (hsucc : ∀ j : Fin d, f (b j.succ) = μ • b j.succ + b j.castSucc) :
-- imply
  LinearMap.toMatrix b b f = jordanBlock (d + 1) μ := by
-- proof
  apply LinearMap.toMatrix_eq_jordanBlock d b f μ hzero hsucc

/--
[toMatrix_eq_blockDiagonal_jordanBlock](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean)
-/
@[path]
private lemma toMatrix_eq_blockDiagonal_jordanBlock_eq
  [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {d : ι → ℕ}
  {b : Basis (Σ i, Fin (d i + 1)) K V}
  {f : Module.End K V}
  {μ : ι → K}
-- given
  (hzero : ∀ i, f (b ⟨i, 0⟩) = μ i • b ⟨i, 0⟩)
  (hsucc : ∀ i (j : Fin (d i)), f (b ⟨i, j.succ⟩) = μ i • b ⟨i, j.succ⟩ + b ⟨i, j.castSucc⟩) :
-- imply
  LinearMap.toMatrix b b f =
    Matrix.blockDiagonal' (fun i ↦ jordanBlock (d i + 1) (μ i)) := by
-- proof
  apply LinearMap.toMatrix_eq_blockDiagonal_jordanBlock d b f μ hzero hsucc

/--
[exists_jordanBasis_of_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean)
-/
@[path]
private lemma exists_jordanBasis_of_isNilpotent_eq
  [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : Module.End K V}
-- given
  (hf : IsNilpotent f) :
-- imply
  ∃ (k : ℕ) (d : Fin k → ℕ) (b : Basis (Σ i, Fin (d i + 1)) K V),
    (∀ i, f (b ⟨i, 0⟩) = 0) ∧
    (∀ i (j : Fin (d i)), f (b ⟨i, j.succ⟩) = b ⟨i, j.castSucc⟩) ∧
    LinearMap.toMatrix b b f =
    Matrix.blockDiagonal' (fun i ↦ jordanBlock (d i + 1) 0) := by
-- proof
  apply Module.End.exists_jordanBasis_of_isNilpotent f hf

/--
[exists_jordanBasis_of_charpoly_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean)
-/
@[path]
private lemma exists_jordanBasis_of_charpoly_splits_eq
  [Field K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : Module.End K V}
-- given
  (hf : f.charpoly.Splits) :
-- imply
  ∃ (k : ℕ) (d : Fin k → ℕ) (μ : Fin k → K)
    (b : Basis (Σ i, Fin (d i + 1)) K V),
    (∀ i, f (b ⟨i, 0⟩) = μ i • b ⟨i, 0⟩) ∧
    (∀ i (j : Fin (d i)),
    f (b ⟨i, j.succ⟩) = μ i • b ⟨i, j.succ⟩ + b ⟨i, j.castSucc⟩) ∧
    LinearMap.toMatrix b b f =
    Matrix.blockDiagonal' (fun i ↦ jordanBlock (d i + 1) (μ i)) := by
-- proof
  apply Module.End.exists_jordanBasis_of_charpoly_splits f hf

/--
[exists_jordan_normal_form_of_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/JordanNormalForm.lean)
-/
@[path]
private lemma exists_jordan_normal_form_of_splits_eq
  [Field K] [Fintype n] [DecidableEq n]
  {A : Matrix n n K}
-- given
  (h : A.charpoly.Splits) :
-- imply
  ∃ (k : ℕ) (s : Fin k → ℕ) (μ : Fin k → K) (P : Matrix n n K)
    (e : (Σ i, Fin (s i)) ≃ n),
    (∀ i, 0 < s i) ∧ IsUnit P ∧
    A = P * Matrix.reindex e e
    (Matrix.blockDiagonal' (fun i => jordanBlock (s i) (μ i))) * P⁻¹ := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted.exists_jordan_normal_form_of_splits A h


-- created on 2026-10-20
