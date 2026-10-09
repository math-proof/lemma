import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.RussoDye

/--
[cStarAlgebra_russoDye](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/RussoDye.lean)
-/
@[path]
private lemma cStarAlgebra_russoDye_eq
-- given
  (A : Type*) [CStarAlgebra A] :
-- imply
  (closure (convexHull ℝ (unitary A : Set A)) = Metric.closedBall (0 : A) 1) :=
-- proof
  Analysis.CStarAlgebra.LandmarkWanted.cStarAlgebra_russoDye A


-- created on 2026-10-09
