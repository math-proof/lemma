import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.HadamardCirculantCore
open MetaMathlibExt


/--
[exists_hadamard_matrix_with_circulant_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardCirculantCore.lean)
-/
@[path]
private lemma exists_hadamard_matrix_with_circulant_core_eq
  :
-- imply
  ∀ (n : ℕ),
    ((Nat.Prime n ∧ n % 4 = 3) ∨
    (∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) ∧ n = p * (p + 2))) →
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
    isHadamardMatrix (n + 1) H ∧ hasCirculantCore n H := by
-- proof
  apply MetaMathlibExt.exists_hadamard_matrix_with_circulant_core

/--
[isHadamardMatrix_iff_isHadamard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardCirculantCore.lean)
-/
@[path]
private lemma isHadamardMatrix_iff_isHadamard_eq
  {m : ℕ}
  {H : Matrix (Fin m) (Fin m) ℤ} :
-- imply
  isHadamardMatrix m H ↔ H.IsHadamard := by
-- proof
  apply MetaMathlibExt.isHadamardMatrix_iff_isHadamard

/--
[hasCirculantCore_iff_circulant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardCirculantCore.lean)
-/
@[path]
private lemma hasCirculantCore_iff_circulant_eq
  {n : ℕ}
  {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} :
-- imply
  hasCirculantCore n H ↔
    ∃ v : Fin n → ℤ, H.submatrix Fin.succ Fin.succ = Matrix.circulant v := by
-- proof
  apply MetaMathlibExt.hasCirculantCore_iff_circulant

/--
[exists_isHadamard_with_circulant_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardCirculantCore.lean)
-/
@[path]
private lemma exists_isHadamard_with_circulant_core_eq
  :
-- imply
  ∀ (n : ℕ),
    ((Nat.Prime n ∧ n % 4 = 3) ∨
    (∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) ∧ n = p * (p + 2))) →
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
    H.IsHadamard ∧ ∃ v : Fin n → ℤ,
    H.submatrix Fin.succ Fin.succ = Matrix.circulant v := by
-- proof
  apply MetaMathlibExt.exists_isHadamard_with_circulant_core


-- created on 2026-10-20
