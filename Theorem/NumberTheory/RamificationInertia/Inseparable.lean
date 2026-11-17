/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/Inseparable.lean -/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.PurelyInseparable.Basic
open scoped Pointwise

public section

namespace Ideal

attribute [local instance] Ideal.Quotient.field
end Ideal
