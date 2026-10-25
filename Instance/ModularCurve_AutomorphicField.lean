-- Carved from Lemma/Definitions/Def_ModularCurve_AutomorphicField.lean: instance decls only.
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Lemma.ModularCurve.AutomorphicField

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace ModularCurve

instance holRing.instNontrivial : Nontrivial ↥holRing :=
  ⟨⟨0, 1, fun h => by simpa using congrArg (fun f : ↥holRing => (f : ℍ → ℂ) UpperHalfPlane.I) h⟩⟩

instance holRing.instNoZeroDivisors : NoZeroDivisors ↥holRing where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    have h' : (f : ℍ → ℂ) * (g : ℍ → ℂ) = 0 := by simpa using congrArg (fun x : ↥holRing => (x : ℍ → ℂ)) h
    rcases (UpperHalfPlane.mul_eq_zero_iff f.2 g.2).1 h' with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h0)

instance holRing.instIsDomain : IsDomain ↥holRing := NoZeroDivisors.to_isDomain _

end ModularCurve


namespace ModularCurve

section

variable (Γ : Subgroup (GL (Fin 2) ℝ))

variable {Γ}

variable [Γ.HasDetOne]

variable (Γ)

variable {Γ}

variable (Γ)

instance automorphicField.instAlgebra : Algebra ℂ ↥(automorphicField Γ) :=
  (automorphicField.constHom Γ).toAlgebra

instance automorphicField.instIsScalarTower :
    IsScalarTower ℂ ↥(automorphicField Γ) (FractionRing ↥holRing) :=
  IsScalarTower.of_algebraMap_eq (fun c => (automorphicField.algebraMap_def Γ c).symm)

end

end ModularCurve

end
