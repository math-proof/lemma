import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.GaloisAction.Part3
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section Stabilizer

variable (𝔫 : Ideal C)

@[reducible]
noncomputable def instMulSemiringActionStabilizer :
    MulSemiringAction (MulAction.stabilizer G 𝔫) (AdicCompletion 𝔫 C) :=
  mulSemiringActionOfSMulEq 𝔫 (fun d => d.2)

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instMulSemiringActionStabilizer

end Stabilizer
end AdicCompletion
