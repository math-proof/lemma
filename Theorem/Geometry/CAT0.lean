/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean -/

import Mathlib.Topology.MetricSpace.Isometry
import Def.Geometry.CAT0
universe u v

/-!
# CAT(0) four-point comparison condition

This file defines the Berg--Nikolaev four-point comparison condition. For geodesic metric spaces,
this condition characterizes CAT(0) spaces. The definition is stated for an arbitrary metric space
because Mathlib does not yet provide a generic geodesic-space API.
-/


-- An inhabited singleton is a basic example.
example : IsCAT0FourPoint PUnit := IsCAT0FourPoint.of_subsingleton PUnit

-- The empty metric space is the boundary case; the comparison is vacuous.
example : IsCAT0FourPoint Empty := IsCAT0FourPoint.of_subsingleton Empty

