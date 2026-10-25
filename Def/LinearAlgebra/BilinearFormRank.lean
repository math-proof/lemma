/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
/-!
# Rank of a bilinear form

This file proves that the rank of the matrix of a bilinear form is independent of the chosen
basis.
-/


namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end LinearMap.BilinForm
namespace MathlibExt.LinearAlgebra.BilinearFormRankWanted

/--
The rank of a bilinear form: the rank of its Gram matrix in any basis.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.
-/
noncomputable def bilinFormRank {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K V) (B : LinearMap.BilinForm K V) : ℕ :=
  (LinearMap.BilinForm.toMatrix b B).rank

end MathlibExt.LinearAlgebra.BilinearFormRankWanted
