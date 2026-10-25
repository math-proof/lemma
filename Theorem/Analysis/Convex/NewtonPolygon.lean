/-
Author: @toskua, Avocado
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Instances.RealVectorSpace
import Def.Analysis.Convex.NewtonPolygon
/-!
# Newton polygon for bivariate polynomials

This module defines the Newton support, Newton polygon, its interior and
frontier, and edge restrictions for bivariate polynomials.
-/


noncomputable section

namespace Convex.NewtonPolygon

variable {k : Type*} [CommSemiring k]

/-- Membership characterization for the Newton support. -/
theorem mem_newtonSupport {f : MvPolynomial (Fin 2) k}
    {x : Fin 2 → Real} :
    x ∈ newtonSupport f ↔ ∃ e ∈ f.support, exponentToReal e = x := by
  simp [newtonSupport]

/-- Newton support of zero is empty. -/
@[simp]
theorem newtonSupport_zero :
    newtonSupport (0 : MvPolynomial (Fin 2) k) = ∅ := by
  simp [newtonSupport]

/-- Newton polygon of zero is empty. -/
@[simp]
theorem newtonPolygon_zero :
    newtonPolygon (0 : MvPolynomial (Fin 2) k) = ∅ := by
  simp [newtonPolygon, newtonSupport_zero]

/-- Support is contained in its convex hull polygon. -/
theorem newtonSupport_subset_newtonPolygon (f : MvPolynomial (Fin 2) k) :
    newtonSupport f ⊆ newtonPolygon f :=
  subset_convexHull ℝ _

/-- Interior is contained in the polygon. -/
theorem newtonPolygonInterior_subset_newtonPolygon
    (f : MvPolynomial (Fin 2) k) :
    newtonPolygonInterior f ⊆ newtonPolygon f :=
  interior_subset

/-- Restriction to the empty set vanishes. -/
@[simp]
theorem edgeRestriction_empty (f : MvPolynomial (Fin 2) k) :
    edgeRestriction f ∅ = 0 := by
  simp [edgeRestriction]

/-- Restriction to the universal set recovers `f`. -/
@[simp]
theorem edgeRestriction_univ (f : MvPolynomial (Fin 2) k) :
    edgeRestriction f Set.univ = f := by
  unfold edgeRestriction
  simp only [Set.mem_univ, ite_true]
  exact (MvPolynomial.as_sum f).symm

end Convex.NewtonPolygon
end
