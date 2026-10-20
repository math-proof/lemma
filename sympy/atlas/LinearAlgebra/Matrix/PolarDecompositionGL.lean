/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PolarDecompositionGL.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import sympy.atlas.LinearAlgebra.Matrix.Factorizations.Polar
/-!
# Polar decomposition of invertible real and complex matrices

This file specializes the bundled `RCLike` polar decomposition to real orthogonal and complex
unitary matrices.
-/

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Polar decomposition in `GL(n, ℝ)`: every invertible real matrix is uniquely the product of an
orthogonal matrix and a positive-definite symmetric matrix.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Endomorphisms / polar decompositions in GL(n, ℝ); R. A. Horn and C. R. Johnson, Matrix Analysis,
2nd ed., Cambridge University Press (2013), Theorem 7.3.1.

Proves `Wanted` entry `polar_decomposition_gl_real`.

Proof: Specialize `Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det` to `ℝ`, where the
unitary group is the orthogonal group, and unbundle its unitary witness. The generic proof takes
`P` to be the CFC square root of `Aᴴ * A` and `U = A * P⁻¹`, the construction in Wikipedia,
"Polar decomposition".
-/
theorem polar_decomposition_gl_real (A : Matrix n n ℝ) (hA : IsUnit A.det) :
    ∃ O S : Matrix n n ℝ,
      O ∈ Matrix.orthogonalGroup n ℝ ∧ S.PosDef ∧ A = O * S ∧
        ∀ O' S' : Matrix n n ℝ,
          O' ∈ Matrix.orthogonalGroup n ℝ → S'.PosDef → A = O' * S' → O' = O ∧ S' = S := by
  obtain ⟨U, P, hP, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det A hA
  refine ⟨U, P, U.property, hP, hdecomp, ?_⟩
  intro O' S' hO' hS' hdecomp'
  obtain ⟨hO, hS⟩ := huniq ⟨O', hO'⟩ S' hS' hdecomp'
  exact ⟨congrArg Subtype.val hO, hS⟩

/--
Polar decomposition in `GL(n, ℂ)`: every invertible complex matrix is uniquely the product of
a unitary matrix and a positive-definite Hermitian matrix.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Endomorphisms / polar decompositions in GL(n, ℂ); R. A. Horn and C. R. Johnson, Matrix Analysis,
2nd ed., Cambridge University Press (2013), Theorem 7.3.1.

Proves `Wanted` entry `polar_decomposition_gl_complex`.

Proof: Specialize `Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det` to `ℂ` and unbundle
its unitary witness. The generic proof takes `P` to be the CFC square root of `Aᴴ * A` and
`U = A * P⁻¹`, the construction in Wikipedia, "Polar decomposition".
-/
theorem polar_decomposition_gl_complex (A : Matrix n n ℂ) (hA : IsUnit A.det) :
    ∃ U P : Matrix n n ℂ,
      U ∈ Matrix.unitaryGroup n ℂ ∧ P.PosDef ∧ A = U * P ∧
        ∀ U' P' : Matrix n n ℂ,
          U' ∈ Matrix.unitaryGroup n ℂ → P'.PosDef → A = U' * P' → U' = U ∧ P' = P := by
  obtain ⟨V, Q, hQ, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det (n := n) (𝕜 := ℂ) A hA
  refine ⟨V, Q, V.property, hQ, hdecomp, ?_⟩
  intro U' P' hU' hP' hdecomp'
  obtain ⟨hU, hP⟩ := huniq ⟨U', hU'⟩ P' hP' hdecomp'
  exact ⟨congrArg Subtype.val hU, hP⟩

end MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted
