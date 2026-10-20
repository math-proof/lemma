import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.ZagierMatrixInverse
open scoped BigOperators
open MetaMathlibExt


/--
[zagier_matrix_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ZagierMatrixInverse.lean)
-/
@[path]
private lemma zagier_matrix_inverse_eq
  {K : ℕ}
-- given
  (hK : 1 < K) :
-- imply
  (Matrix.of (fun i j : Fin (K - 1) =>
    (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
    ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
    (↑(Nat.choose (2 * (j.val + 1) - 1)
    (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
    (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
    Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    =
    (Matrix.of (fun i j : Fin (K - 1) =>
    (-2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
    ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
    (↑(Nat.choose (2 * K - 2 * (j.val + 1))
    (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
    (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
    Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    ∧ (Matrix.of (fun i j : Fin (K - 1) =>
    (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (i.val + 1) - 1)) : ℚ) +
    (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1))) : ℚ)) :
    Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    * (Matrix.of (fun i j : Fin (K - 1) =>
    (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
    ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
    (↑(Nat.choose (2 * (j.val + 1) - 1)
    (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
    (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
    Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    = 1
    ∧ (Matrix.of (fun i j : Fin (K - 1) =>
    (2 : ℚ) / (2 * (↑(i.val + 1) : ℚ) - 1) *
    ∑ n ∈ Finset.range (2 * K - 2 * (i.val + 1) + 1),
    (↑(Nat.choose (2 * (j.val + 1) - 1)
    (2 * K - 2 * (i.val + 1) - n + 1)) : ℚ) *
    (↑(Nat.choose (n + 2 * (i.val + 1) - 2) n) : ℚ) * bernoulli n) :
    Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    * (Matrix.of (fun i j : Fin (K - 1) =>
    (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * (i.val + 1) - 1)) : ℚ) +
    (↑(Nat.choose (2 * K - 2 * (j.val + 1)) (2 * K - 2 * (i.val + 1))) : ℚ)) :
    Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ)
    = 1 := by
-- proof
  apply MetaMathlibExt.zagier_matrix_inverse K hK


-- created on 2026-10-20
