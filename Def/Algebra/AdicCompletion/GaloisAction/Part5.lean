import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.GaloisAction.Part5
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section LiesOver

variable {O : Type w} [CommRing O] [Algebra O C] (J : Ideal O) (𝔫 : Ideal C)

noncomputable def algHomOfLiesOver [𝔫.LiesOver J] :
    AdicCompletion J O →ₐ[O] AdicCompletion 𝔫 C :=
  mapₐ J 𝔫 (Algebra.ofId O C) (map_ofId_le_of_liesOver J 𝔫)

@[reducible]
noncomputable def instAlgebraOfLiesOver [𝔫.LiesOver J] :
    Algebra (AdicCompletion J O) (AdicCompletion 𝔫 C) :=
  (algHomOfLiesOver J 𝔫).toRingHom.toAlgebra

scoped[AdicCompletion.GaloisAction] attribute [instance low] AdicCompletion.instAlgebraOfLiesOver

end LiesOver
end AdicCompletion
