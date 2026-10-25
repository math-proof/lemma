-- Carved from Lemma/Definitions/Def_DrinfeldCurve_MapConstants.lean: instance decls only.
import Lemma.DrinfeldCurve.FunctionField
import Lemma.AlgebraicCurve.Correspondence
import Lemma.DrinfeldCurve.MapConstants

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace DrinfeldCurve

section Square

variable (q : ℕ) (k k' : Type) [Field k] [Field k'] [Algebra k k']


scoped instance instTowerConstantsFunctionField :
    @IsScalarTower k k' (drinfeldFunctionField q k')
      (Algebra.toSMul (R := k) (A := k'))
      (Algebra.toSMul (R := k') (A := drinfeldFunctionField q k'))
      (Algebra.toSMul (R := k) (A := drinfeldFunctionField q k')) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance instTowerFunctionFieldConstants [IsDomain (CoordRing q k')] :
    @IsScalarTower k (drinfeldFunctionField q k) (drinfeldFunctionField q k')
      (Algebra.toSMul (R := k) (A := drinfeldFunctionField q k))
      (Algebra.toSMul (R := drinfeldFunctionField q k) (A := drinfeldFunctionField q k'))
      (Algebra.toSMul (R := k) (A := drinfeldFunctionField q k')) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [algebraMap_drinfeldFunctionField_eq,
      IsScalarTower.algebraMap_apply k (CoordRing q k) (drinfeldFunctionField q k) c,
      functionFieldMapConstants_algebraMap, CoordRing.mapConstants_algebraMap]
    rfl


end Square

end DrinfeldCurve

end
