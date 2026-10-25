import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.GaloisAction.Part2
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

@[reducible]
noncomputable def mulSemiringActionOfSMulEq (h : ∀ g : G, g • I = I) :
    MulSemiringAction G (AdicCompletion I C) where
  smul g x := smulAlgHom I h g x
  one_smul x := by
    apply ext_evalₐ
    intro n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    show evalₐ I n (smulAlgHom I h 1 x) = _
    rw [evalₐ_smulAlgHom I h 1 n c x hc.symm, one_smul, hc]
  mul_smul g g' x := by
    apply ext_evalₐ
    intro n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
    show evalₐ I n (smulAlgHom I h (g * g') x)
      = evalₐ I n (smulAlgHom I h g (smulAlgHom I h g' x))
    rw [evalₐ_smulAlgHom I h (g * g') n c x hc.symm,
      evalₐ_smulAlgHom I h g n (g' • c) _ (evalₐ_smulAlgHom I h g' n c x hc.symm), mul_smul]
  smul_zero g := _root_.map_zero (smulAlgHom I h g)
  smul_add g x y := _root_.map_add (smulAlgHom I h g) x y
  smul_one g := _root_.map_one (smulAlgHom I h g)
  smul_mul g x y := _root_.map_mul (smulAlgHom I h g) x y

end Generic
end AdicCompletion
