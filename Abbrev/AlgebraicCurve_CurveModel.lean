import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Class.AlgebraicCurve_DivisorClassGroup
import Structure.AlgebraicCurve_CurveModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve


namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

abbrev functionFieldAlgebra (M : CurveModel K L) : Algebra K M.C.functionField :=
  (baseToFunctionField M.toBase).toAlgebra

end CurveModel

end AlgebraicCurve

end
