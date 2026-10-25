import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.GaloisAction
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section Generic

variable (I : Ideal C)

noncomputable def smulAlgHom (h : ∀ g : G, g • I = I) (g : G) :
    AdicCompletion I C →ₐ[ℤ] AdicCompletion I C :=
  mapₐ I I (MulSemiringAction.toRingHom G C g).toIntAlgHom (map_toIntAlgHom_le_of_smul_eq I g (h g))

end Generic
end AdicCompletion
