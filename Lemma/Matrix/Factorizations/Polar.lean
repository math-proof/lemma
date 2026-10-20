import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Factorizations.Polar
open Matrix
open scoped ComplexOrder


/--
[exists_unitaryGroup_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
private lemma exists_unitaryGroup_posSemidef_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ} :
-- imply
  ∃ (U : Matrix.unitaryGroup n ℂ) (P : Matrix n n ℂ),
    P.PosSemidef ∧ P * P = Aᴴ * A ∧ A = (U : Matrix n n ℂ) * P := by
-- proof
  apply Matrix.exists_unitaryGroup_posSemidef A

/--
[exists_unique_unitaryGroup_posDef_of_isUnit_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
private lemma exists_unique_unitaryGroup_posDef_of_isUnit_det_eq
  [Fintype n] [RCLike 𝕜] [DecidableEq n]
  {A : Matrix n n 𝕜}
-- given
  (hA : IsUnit A.det) :
-- imply
  ∃ (U : Matrix.unitaryGroup n 𝕜) (P : Matrix n n 𝕜),
    P.PosDef ∧ A = (U : Matrix n n 𝕜) * P ∧
    ∀ (U' : Matrix.unitaryGroup n 𝕜) (P' : Matrix n n 𝕜),
    P'.PosDef → A = (U' : Matrix n n 𝕜) * P' → U' = U ∧ P' = P := by
-- proof
  apply Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det A hA


-- created on 2026-10-20
