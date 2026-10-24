/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/NewtonPolygon.lean -/


import sympy.atlas.Analysis.Convex.NewtonPolygon

/-!
# Tests for Newton polygons

Checks for zero support, polygon, interior, frontier, edge restrictions,
and monomial point membership.
-/

noncomputable section


namespace NewtonPolygonTest

/-- Zero has empty support. -/
example : NewtonPolygon.newtonSupport (0 : MvPolynomial (Fin 2) ℕ) = ∅ := by
  simp

/-- Zero has empty polygon. -/
example : NewtonPolygon.newtonPolygon (0 : MvPolynomial (Fin 2) ℕ) = ∅ := by
  simp

/-- Zero polygon has empty interior. -/
example :
    NewtonPolygon.newtonPolygonInterior (0 : MvPolynomial (Fin 2) ℕ) = ∅ := by
  simp [NewtonPolygon.newtonPolygonInterior, NewtonPolygon.newtonPolygon_zero]

/-- Zero polygon has empty frontier. -/
example :
    NewtonPolygon.newtonPolygonBoundary (0 : MvPolynomial (Fin 2) ℕ) = ∅ := by
  simp [NewtonPolygon.newtonPolygonBoundary, NewtonPolygon.newtonPolygon_zero]

/-- Empty restriction vanishes. -/
example (f : MvPolynomial (Fin 2) ℕ) :
    NewtonPolygon.edgeRestriction f ∅ = 0 := by
  simp

/-- Unrestricted restriction recovers the polynomial. -/
example (f : MvPolynomial (Fin 2) ℕ) :
    NewtonPolygon.edgeRestriction f Set.univ = f := by
  simp

/-- A monomial exponent lies in its Newton support. -/
example (e : Fin 2 →₀ Nat) :
    NewtonPolygon.exponentToReal e ∈ NewtonPolygon.newtonSupport
      (MvPolynomial.monomial e 1 : MvPolynomial (Fin 2) ℕ) := by
  rw [NewtonPolygon.mem_newtonSupport]
  refine ⟨e, ?_, rfl⟩
  rw [MvPolynomial.support_monomial, ite_eq_right one_ne_zero]
  exact Finset.mem_singleton_self e

/-- A monomial exponent lies in its Newton polygon. -/
example (e : Fin 2 →₀ Nat) :
    NewtonPolygon.exponentToReal e ∈ NewtonPolygon.newtonPolygon
      (MvPolynomial.monomial e 1 : MvPolynomial (Fin 2) ℕ) := by
  apply NewtonPolygon.newtonSupport_subset_newtonPolygon
  rw [NewtonPolygon.mem_newtonSupport]
  refine ⟨e, ?_, rfl⟩
  rw [MvPolynomial.support_monomial, ite_eq_right one_ne_zero]
  exact Finset.mem_singleton_self e

end NewtonPolygonTest
