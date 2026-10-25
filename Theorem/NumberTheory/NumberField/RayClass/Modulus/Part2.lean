/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Instance.NumberTheory.NumberField.RayClass.Modulus
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

@[simp] theorem one_finitePart : (1 : Modulus K).finitePart = 1 := rfl

@[simp] theorem one_infinitePart : (1 : Modulus K).infinitePart = ∅ := rfl

@[simp] theorem mul_finitePart (m n : Modulus K) :
    (m * n).finitePart = m.finitePart * n.finitePart := rfl

open Classical in
@[simp] theorem mul_infinitePart (m n : Modulus K) :
    (m * n).infinitePart = m.infinitePart ∪ n.infinitePart := rfl

end Modulus
end NumberField
