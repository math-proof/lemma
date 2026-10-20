/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/CAT0.lean -/

import Mathlib.Topology.MetricSpace.Isometry

/-!
# CAT(0) four-point comparison condition

This file defines the Berg--Nikolaev four-point comparison condition. For geodesic metric spaces,
this condition characterizes CAT(0) spaces. The definition is stated for an arbitrary metric space
because Mathlib does not yet provide a generic geodesic-space API.
-/

universe u v

/-- A metric space satisfies the CAT(0) four-point comparison condition if the sum of the squares
of the diagonals of every quadrilateral is at most the sum of the squares of its sides.

For geodesic metric spaces this is equivalent to the usual Euclidean comparison-triangle
definition of a CAT(0) space. -/
def IsCAT0FourPoint (X : Type u) [MetricSpace X] : Prop :=
  ∀ x y z w : X,
    dist x z ^ 2 + dist y w ^ 2 ≤
      dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2

/-- The defining four-point characterization of `IsCAT0FourPoint`. -/
theorem isCAT0FourPoint_iff {X : Type u} [MetricSpace X] :
    IsCAT0FourPoint X ↔
      ∀ x y z w : X,
        dist x z ^ 2 + dist y w ^ 2 ≤
          dist x y ^ 2 + dist y z ^ 2 + dist z w ^ 2 + dist w x ^ 2 :=
  Iff.rfl

namespace IsCAT0FourPoint

/-- The CAT(0) four-point condition pulls back along an isometry. -/
theorem of_isometry {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (hY : IsCAT0FourPoint Y) {f : X → Y} (hf : Isometry f) : IsCAT0FourPoint X := by
  intro x y z w
  simpa only [hf.dist_eq] using hY (f x) (f y) (f z) (f w)

/-- The CAT(0) four-point condition is invariant under isometric equivalence. -/
theorem iff_of_isometryEquiv {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) : IsCAT0FourPoint X ↔ IsCAT0FourPoint Y :=
  ⟨fun hX ↦ of_isometry hX e.symm.isometry, fun hY ↦ of_isometry hY e.isometry⟩

/-- Every subsingleton metric space satisfies the CAT(0) four-point condition. -/
theorem of_subsingleton (X : Type u) [MetricSpace X] [Subsingleton X] : IsCAT0FourPoint X := by
  intro x y z w
  have hxy : x = y := Subsingleton.elim _ _
  have hxz : x = z := Subsingleton.elim _ _
  have hxw : x = w := Subsingleton.elim _ _
  subst y
  subst z
  subst w
  simp

end IsCAT0FourPoint

-- An inhabited singleton is a basic example.
example : IsCAT0FourPoint PUnit := IsCAT0FourPoint.of_subsingleton PUnit

-- The empty metric space is the boundary case; the comparison is vacuous.
example : IsCAT0FourPoint Empty := IsCAT0FourPoint.of_subsingleton Empty
