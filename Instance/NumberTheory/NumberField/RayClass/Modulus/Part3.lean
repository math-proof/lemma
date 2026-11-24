module
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Def.NumberTheory.NumberField.RayClass.Modulus


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Moduli for ray class groups (N403 foundation)

Multiplication on the infinite part uses union of real-place sets.
This represents truncated exponent addition `min (m v + n v) 1`:
a real place appears in the product iff it appears in either factor.
The ATLAS-extracted `max` formula for this operation was a typo.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

instance : Dvd (Modulus K) := ⟨divides⟩

end Modulus
end NumberField
