/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean -/

import Mathlib.Topology.MetricSpace.Isometry
universe u v

/-!
# CAT(0) four-point comparison condition

This file defines the Berg--Nikolaev four-point comparison condition. For geodesic metric spaces,
this condition characterizes CAT(0) spaces. The definition is stated for an arbitrary metric space
because Mathlib does not yet provide a generic geodesic-space API.
-/


/-- A metric space satisfies the CAT(0) four-point comparison condition if the sum of the squares
of the diagonals of every quadrilateral is at most the sum of the squares of its sides.

For geodesic metric spaces this is equivalent to the usual Euclidean comparison-triangle
definition of a CAT(0) space. -/
def IsCAT0FourPoint (X : Type u) [MetricSpace X] : Prop :=
  ∀ x y z w : X,
    dist x z ^ 2 + dist y w ^ 2 ≤
      dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2

