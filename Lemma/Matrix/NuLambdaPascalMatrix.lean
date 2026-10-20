import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.NuLambdaPascalMatrix
open scoped BigOperators
open MetaMathlibExt


/--
[IsNuLambdaPascalMatrix.finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
private lemma IsNuLambdaPascalMatrix_finite_support_eq
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
  {i j : ℕ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
  (hij : 2 * n ≤ i ∨ 2 * n ≤ j) :
-- imply
  S i j = 0 := by
-- proof
  apply MetaMathlibExt.IsNuLambdaPascalMatrix.finite_support N n nu lam beta S hn h i j hij

/--
[IsNuLambdaPascalMatrix.skew](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
private lemma IsNuLambdaPascalMatrix_skew_eq
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
  {i j : ℕ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn) :
-- imply
  S i j = -S j i := by
-- proof
  apply MetaMathlibExt.IsNuLambdaPascalMatrix.skew N n nu lam beta S hn h i j

/--
[IsNuLambdaPascalMatrix.corner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
private lemma IsNuLambdaPascalMatrix_corner_eq
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn) :
-- imply
  S (2 * n - 2) (2 * n - 1) = 1 := by
-- proof
  apply MetaMathlibExt.IsNuLambdaPascalMatrix.corner N n nu lam beta S hn h

/--
[IsNuLambdaPascalMatrix.last_column](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
private lemma IsNuLambdaPascalMatrix_last_column_eq
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
  {j : ℕ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
  (hj : j < 2 * n - 2) :
-- imply
  S j (2 * n - 1) = ∑ t : Fin N, beta t * S (j + t.val + 1) (2 * n - 1) := by
-- proof
  apply MetaMathlibExt.IsNuLambdaPascalMatrix.last_column N n nu lam beta S hn h j hj

/--
[IsNuLambdaPascalMatrix.interior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
private lemma IsNuLambdaPascalMatrix_interior_eq
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
  {i j : ℕ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn)
  (hi : i < 2 * n - 1)
  (hj : j < 2 * n - 1) :
-- imply
  S i j = lam * S (i + 1) (j + 1) + nu * (S (i + 1) j + S i (j + 1)) := by
-- proof
  apply MetaMathlibExt.IsNuLambdaPascalMatrix.interior N n nu lam beta S hn h i j hi hj


-- created on 2026-10-20
