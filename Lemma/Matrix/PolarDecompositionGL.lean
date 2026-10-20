import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.PolarDecompositionGL
open scoped ComplexOrder
open MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted


/--
[polar_decomposition_gl_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PolarDecompositionGL.lean)
-/
@[path]
private lemma polar_decomposition_gl_real_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℝ}
-- given
  (hA : IsUnit A.det) :
-- imply
  ∃ O S : Matrix n n ℝ,
    O ∈ Matrix.orthogonalGroup n ℝ ∧ S.PosDef ∧ A = O * S ∧
    ∀ O' S' : Matrix n n ℝ,
    O' ∈ Matrix.orthogonalGroup n ℝ → S'.PosDef → A = O' * S' → O' = O ∧ S' = S := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted.polar_decomposition_gl_real A hA

/--
[polar_decomposition_gl_complex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PolarDecompositionGL.lean)
-/
@[path]
private lemma polar_decomposition_gl_complex_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ}
-- given
  (hA : IsUnit A.det) :
-- imply
  ∃ U P : Matrix n n ℂ,
    U ∈ Matrix.unitaryGroup n ℂ ∧ P.PosDef ∧ A = U * P ∧
    ∀ U' P' : Matrix n n ℂ,
    U' ∈ Matrix.unitaryGroup n ℂ → P'.PosDef → A = U' * P' → U' = U ∧ P' = P := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted.polar_decomposition_gl_complex A hA


-- created on 2026-10-20
