import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Hankel
open Matrix


/--
[hankel_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Hankel.lean)
-/
@[path]
private lemma hankel_apply_eq
  {s : ℕ → α}
  {i j : ℕ} :
-- imply
  hankel s i j = s (i + j) := by
-- proof
  apply Matrix.hankel_apply s i j

/--
[hankelFin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Hankel.lean)
-/
@[path]
private lemma hankelFin_apply_eq
  {n : ℕ}
  {s : ℕ → α}
  {i j : Fin n} :
-- imply
  hankelFin n s i j = s (i + j) := by
-- proof
  apply Matrix.hankelFin_apply n s i j


-- created on 2026-10-20
