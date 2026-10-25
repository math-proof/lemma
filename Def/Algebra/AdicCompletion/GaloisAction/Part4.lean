import Mathlib
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
import Theorem.Algebra.AdicCompletion.GaloisAction.Part4
set_option autoImplicit false

open scoped Pointwise


namespace AdicCompletion.GaloisAction

end AdicCompletion.GaloisAction

namespace AdicCompletion

open scoped AdicCompletion.GaloisAction

universe u v w

variable {C : Type u} [CommRing C] {G : Type v} [Group G] [MulSemiringAction G C]

section MapIdeal

variable {O : Type w} [CommRing O] [Algebra O C]

@[reducible]
noncomputable def instMulSemiringActionMap [SMulCommClass G O C] (J : Ideal O) :
    MulSemiringAction G (AdicCompletion (J.map (algebraMap O C)) C) :=
  mulSemiringActionOfSMulEq _ (smul_map_algebraMap_eq J)

scoped[AdicCompletion.GaloisAction] attribute [instance] AdicCompletion.instMulSemiringActionMap

end MapIdeal
end AdicCompletion
