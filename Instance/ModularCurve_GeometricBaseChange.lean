-- Carved from Lemma/Definitions/Def_ModularCurve_GeometricBaseChange.lean: instance decls only.
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Instance.FieldTheory_RatAlgClosureGalois
public import Theorem.LaurentSeries.GeometricBaseChange
public import Def.ModularCurve_GeometricBaseChange
@[expose] public section

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
