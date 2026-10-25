-- Carved from Lemma/Definitions/Def_ModularCurve_GeometricBaseChange.lean: instance decls only.
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Module.LinearMap.Rat
import Lemma.ModularCurve.LaurentCoeff
import Instance.FieldTheory_RatAlgClosureGalois
import Lemma.ModularCurve.GeometricBaseChange

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open IntermediateField

namespace ModularCurve


section BaseChange

variable (L : Type*) [Field L]

variable [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

instance instIsDomainTensorProduct : IsDomain (L ⊗[ℚ] F₀) :=
  Function.Injective.isDomain (baseChangeHom L F₀).toRingHom (baseChangeHom_injective L F₀)

variable [Algebra.IsAlgebraic ℚ L]

end BaseChange

end ModularCurve

end
