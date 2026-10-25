import Instance.DrinfeldCurve_CoordRing
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

noncomputable section

namespace DrinfeldCurve

variable (q : ℕ) (k : Type) [Field k]

abbrev drinfeldFunctionField : Type := FractionRing (CoordRing q k)

variable [Fact q.Prime] [Algebra (GaloisField q 2) k]

end DrinfeldCurve

end
