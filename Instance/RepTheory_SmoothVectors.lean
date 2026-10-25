-- Carved from Lemma/Definitions/Def_RepTheory_SmoothVectors.lean: instance decls only.
import Mathlib
import Instance.Deformations_ContinuousSMulDiscrete
import Lemma.RepTheory.SmoothVectors

set_option autoImplicit false

open scoped Topology

namespace FLT.SmoothVectors


namespace RightTranslationFn

variable {G M : Type*}

instance [AddCommMonoid M] : AddCommMonoid (RightTranslationFn G M) :=
  inferInstanceAs (AddCommMonoid (G → M))

instance [Group G] : MulAction G (RightTranslationFn G M) where
  smul g f := mk fun x => toFun f (x * g)
  one_smul f := ext fun x => congrArg (toFun f) (mul_one x)
  mul_smul g h f := ext fun x => (congrArg (toFun f) (mul_assoc x g h)).symm

instance [Group G] [AddCommMonoid M] : DistribMulAction G (RightTranslationFn G M) where
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

end RightTranslationFn


end FLT.SmoothVectors
