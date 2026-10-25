import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.GaloisAction
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

theorem smulAlgHom_of (h : ∀ g : G, g • I = I) (g : G) (c : C) :
    smulAlgHom I h g (of I C c) = of I C (g • c) := by
  rw [smulAlgHom, mapₐ_of]
  rfl

theorem evalₐ_smulAlgHom (h : ∀ g : G, g • I = I) (g : G) (n : ℕ) (c : C)
    (x : AdicCompletion I C) (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    evalₐ I n (smulAlgHom I h g x) = Ideal.Quotient.mk (I ^ n) (g • c) := by
  rw [smulAlgHom, evalₐ_mapₐ, hx, levelMapₐ_mk]
  rfl

end Generic
end AdicCompletion
