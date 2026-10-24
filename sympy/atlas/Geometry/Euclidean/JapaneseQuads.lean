/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JapaneseQuads.lean -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lemma.Set.Euclidean.CarnotInradius
section
namespace MetaMathlibExt

/-- Rotate a 2D vector by 90 degrees: `(-y, x)`. Perpendicular to the input. -/
private def perp2 (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-(d 1), d 0]
end MetaMathlibExt
end
