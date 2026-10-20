import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.ParametricSard
open MeasureTheory
open MathlibExt.Geometry.Manifold.ParametricSardWanted


/--
[parametricSard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean)
-/
@[path]
private lemma parametricSard_eq
  {p m n : ℕ}
  {F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
  {y : EuclideanSpace ℝ (Fin n)}
-- given
  (hF : ContDiff ℝ ⊤ F)
  (hreg : ∀ a x, F (a, x) = y → Function.Surjective (fderiv ℝ F (a, x))) :
-- imply
  volume (badParameterSet (F := by
-- proof
  apply MathlibExt.Geometry.Manifold.ParametricSardWanted.parametricSard F y hF hreg


-- created on 2026-10-20
