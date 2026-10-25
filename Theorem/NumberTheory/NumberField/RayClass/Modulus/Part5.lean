/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Def.NumberTheory.NumberField.RayClass.Modulus.Part3
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

/-- Finite part of `infinite v` is trivial. -/
@[simp] theorem infinite_finitePart (v : RealPlace K) :
    (infinite v).finitePart = 1 := rfl

/-- Infinite part of `infinite v` is the singleton. -/
@[simp] theorem infinite_infinitePart (v : RealPlace K) :
    (infinite v).infinitePart = {v} := rfl

end Modulus
end NumberField
