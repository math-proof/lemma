import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.HairyBall
open Metric
open scoped Pointwise
open MathlibExt.Geometry.Manifold.HairyBallWanted


/--
[hairyBall_even_sphere_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HairyBall.lean)
-/
@[path]
private lemma hairyBall_even_sphere_ambient_eq
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}
  {f : sphere (0 : E) 1 → E}
-- given
  (hDim : Module.finrank ℝ E = 2 * k + 1)
  (hf : Continuous f)
  (hortho : ∀ x : sphere (0 : E) 1, @inner ℝ E _ (f x) (x : E) = 0) :
-- imply
  ∃ x : sphere (0 : E) 1, f x = 0 := by
-- proof
  apply MathlibExt.Geometry.Manifold.HairyBallWanted.hairyBall_even_sphere_ambient hDim f hf hortho


-- created on 2026-10-20
