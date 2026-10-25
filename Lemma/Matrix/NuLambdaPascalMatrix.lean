import Mathlib
import sympy.Basic
import Def.LinearAlgebra.Matrix.NuLambdaPascalMatrix
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[IsNuLambdaPascalMatrix.finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
lemma IsNuLambdaPascalMatrix.finite_support
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
  S i j = 0 :=
-- proof
  h.1 i j hij

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsNuLambdaPascalMatrix.skew](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
lemma IsNuLambdaPascalMatrix.skew
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
  {i j : ℕ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn) :
-- imply
  S i j = -S j i :=
-- proof
  h.2.1 i j

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsNuLambdaPascalMatrix.corner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
lemma IsNuLambdaPascalMatrix.corner
  {N n : ℕ}
  {nu lam : ℂ}
  {beta : Fin N → ℂ}
  {S : ℕ → ℕ → ℂ}
-- given
  (hn : 0 < n)
  (h : IsNuLambdaPascalMatrix N n nu lam beta S hn) :
-- imply
  S (2 * n - 2) (2 * n - 1) = 1 :=
-- proof
  h.2.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsNuLambdaPascalMatrix.last_column](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
lemma IsNuLambdaPascalMatrix.last_column
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
  S j (2 * n - 1) = ∑ t : Fin N, beta t * S (j + t.val + 1) (2 * n - 1) :=
-- proof
  h.2.2.2.1 j hj

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsNuLambdaPascalMatrix.interior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean)
-/
@[path]
lemma IsNuLambdaPascalMatrix.interior
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
  S i j = lam * S (i + 1) (j + 1) + nu * (S (i + 1) j + S i (j + 1)) :=
-- proof
  h.2.2.2.2 i j hi hj

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
