-- Carved from Lemma/Definitions/Def_ModularCurve_LaurentBaseChangeTower.lean: instance decls only.
import Mathlib
import Lemma.ModularCurve.LaurentCoeff

noncomputable section

namespace ModularCurve

set_option synthInstance.maxHeartbeats 400000

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

section Tower


instance instTowerRatLBaseChange :
    @IsScalarTower ℚ L (laurentBaseChange L F₀)
      (Algebra.toSMul (R := ℚ) (A := L))
      (Algebra.toSMul (R := L) (A := laurentBaseChange L F₀))
      (Algebra.toSMul (R := ℚ) (A := laurentBaseChange L F₀)) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance instTowerRatF₀BaseChange :
    @IsScalarTower ℚ F₀ (laurentBaseChange L F₀)
      (Algebra.toSMul (R := ℚ) (A := F₀))
      (Algebra.toSMul (R := F₀) (A := laurentBaseChange L F₀))
      (Algebra.toSMul (R := ℚ) (A := laurentBaseChange L F₀)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

end Tower

end ModularCurve

end
