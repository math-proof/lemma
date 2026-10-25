-- Carved from Lemma/Definitions/Def_WeierstrassCurve_FunctionFieldQuadratic.lean: instance decls only.
import Mathlib
import Lemma.WeierstrassCurve.FunctionFieldQuadratic

set_option autoImplicit false

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

open CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

instance : Algebra (RatFunc F) W.FunctionField :=
  (ratFuncToFunctionField W).toAlgebra

instance : IsScalarTower F[X] (RatFunc F) W.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun p => (ratFuncToFunctionField_algebraMap p).symm

instance : IsScalarTower F (RatFunc F) W.FunctionField := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F) c,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    Polynomial.algebraMap_eq, algebraMap_polynomial_eq_polyToFunctionField]
  exact (polyToFunctionField_C c).symm

end WeierstrassCurve.Affine

end
