import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Def.Algebra.AdicCompletion.GaloisAction.Part2
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

theorem smul_def' (h : ∀ g : G, g • I = I) (g : G) (x : AdicCompletion I C) :
    (letI := mulSemiringActionOfSMulEq I h; g • x) = smulAlgHom I h g x :=
  rfl

theorem smul_of' (h : ∀ g : G, g • I = I) (g : G) (c : C) :
    (letI := mulSemiringActionOfSMulEq I h; g • of I C c) = of I C (g • c) :=
  smulAlgHom_of I h g c

theorem evalₐ_smul' (h : ∀ g : G, g • I = I) (g : G) (n : ℕ) (c : C) (x : AdicCompletion I C)
    (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) c) :
    (letI := mulSemiringActionOfSMulEq I h; evalₐ I n (g • x)) = Ideal.Quotient.mk (I ^ n) (g • c) :=
  evalₐ_smulAlgHom I h g n c x hx

end Generic
end AdicCompletion
