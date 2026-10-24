import Mathlib

set_option autoImplicit false

universe u

namespace Deformation

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G]
variable {k : Type u} [Field k]

noncomputable def matrixRepresentation (ρ : G →* GL n k) : Representation k G (n → k) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp]
lemma matrixRepresentation_apply (ρ : G →* GL n k) (g : G) :
    matrixRepresentation ρ g = Matrix.mulVecLin (ρ g).val :=
  Matrix.GeneralLinearGroup.coe_toLin _

end Deformation
