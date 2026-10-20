import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.SylvesterGallai
open MathlibExt.Geometry.Euclidean.SylvesterGallaiWanted


/--
[sylvester_gallai](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/SylvesterGallai.lean)
-/
@[path]
private lemma sylvester_gallai_eq
  {s : Set (EuclideanSpace ℝ (Fin 2))}
-- given
  (hs_fin : s.Finite)
  (hs_noncollinear : ¬Collinear ℝ s) :
-- imply
  ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
    ∀ c ∈ s, Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) → c = a ∨ c = b := by
-- proof
  apply MathlibExt.Geometry.Euclidean.SylvesterGallaiWanted.sylvester_gallai s hs_fin hs_noncollinear


-- created on 2026-10-20
