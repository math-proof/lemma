/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/FeuerbachTheorem.lean -/

import Mathlib.Geometry.Euclidean.NinePointCircle
import Mathlib.Geometry.Euclidean.Incenter
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


section WantedAux

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
end WantedAux
namespace MetaMathlibExt

open Affine Affine.Simplex EuclideanGeometry
open scoped InnerProductSpace

end MetaMathlibExt
section
end
