-- Carved from Lemma/Definitions/Def_ModularCurve_ProjectiveLine.lean: instance decls only.
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finite.Prod
import Lemma.ModularCurve.ProjectiveLine

namespace ModularCurve

open Matrix
open scoped MatrixGroups

section ProjectiveLine

variable {R S : Type*} [CommRing R] [CommRing S]

instance unimodularRowSetoid (R : Type*) [CommRing R] : Setoid (UnimodularRow R) where
  r v w := ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
  iseqv := by
    refine ⟨fun v => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨u, h1, h2⟩
      exact ⟨u⁻¹, by rw [← h1, Units.inv_mul_cancel_left],
        by rw [← h2, Units.inv_mul_cancel_left]⟩
    · rintro v w z ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩
      exact ⟨u' * u, by rw [Units.val_mul, mul_assoc, h1, h1'],
        by rw [Units.val_mul, mul_assoc, h2, h2']⟩

instance instFiniteProjectiveLine [Finite R] : Finite (ProjectiveLine R) :=
  Quotient.finite _

end ProjectiveLine


end ModularCurve
