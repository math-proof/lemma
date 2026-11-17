/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/FeuerbachTheorem.lean -/
module

public import Mathlib.Geometry.Euclidean.NinePointCircle
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

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
