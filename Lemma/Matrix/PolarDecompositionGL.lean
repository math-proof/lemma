import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped ComplexOrder


namespace MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted

/--
[polar_decomposition_gl_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PolarDecompositionGL.lean)
-/
@[path]
lemma polar_decomposition_gl_real
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
  obtain ⟨U, P, hP, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det A hA
  refine ⟨U, P, U.property, hP, hdecomp, ?_⟩
  intro O' S' hO' hS' hdecomp'
  obtain ⟨hO, hS⟩ := huniq ⟨O', hO'⟩ S' hS' hdecomp'
  exact ⟨congrArg Subtype.val hO, hS⟩

end MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted

namespace MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted

/--
[polar_decomposition_gl_complex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PolarDecompositionGL.lean)
-/
@[path]
lemma polar_decomposition_gl_complex
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
  obtain ⟨V, Q, hQ, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det (n := n) (𝕜 := ℂ) A hA
  refine ⟨V, Q, V.property, hQ, hdecomp, ?_⟩
  intro U' P' hU' hP' hdecomp'
  obtain ⟨hU, hP⟩ := huniq ⟨U', hU'⟩ P' hP' hdecomp'
  exact ⟨congrArg Subtype.val hU, hP⟩

end MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted


-- created on 2026-10-20
-- updated on 2026-10-26
