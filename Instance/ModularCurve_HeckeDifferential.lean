-- Carved from Lemma/Definitions/Def_ModularCurve_HeckeDifferential.lean: instance decls only.
import Mathlib
import Lemma.ModularCurve.HeckeOperator
import Def.AlgebraicCurve_DifferentialPushPull
import Def.AlgebraicCurve_RegularDifferentials

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve

namespace ModularCurve


section Shortcuts

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

set_option synthInstance.maxHeartbeats 400000 in
instance instAlgebraIntermediateFieldLaurent : Algebra L F := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instModuleKaehlerIntermediateFieldLaurent : Module L Ω[F⁄L] := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instIsScalarTowerKaehlerIntermediateFieldLaurent : IsScalarTower L F Ω[F⁄L] :=
  inferInstance

instance instIsScalarTowerIntermediateFieldLaurent : IsScalarTower L F (LaurentSeries L) :=
  ⟨fun c f x => by
    show ((c • f : F) : LaurentSeries L) * x = c • ((f : LaurentSeries L) * x)
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
      ← C_apply, mul_assoc, C_mul_eq_smul]⟩

end Shortcuts


end ModularCurve

end
