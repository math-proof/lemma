/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Def.NumberTheory.NumberField.RayClass.Modulus.Part2
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

open Classical in
@[simp] theorem gcd_infinitePart (m n : Modulus K) :
    (gcd m n).infinitePart = m.infinitePart ∩ n.infinitePart := rfl

open Classical in
@[simp] theorem lcm_infinitePart (m n : Modulus K) :
    (lcm m n).infinitePart = m.infinitePart ∪ n.infinitePart := rfl

@[simp] theorem gcd_finitePart (m n : Modulus K) :
    ((gcd m n).finitePart : Ideal (𝓞 K)) =
      (m.finitePart : Ideal (𝓞 K)) ⊔ (n.finitePart : Ideal (𝓞 K)) := rfl

@[simp] theorem lcm_finitePart (m n : Modulus K) :
    ((lcm m n).finitePart : Ideal (𝓞 K)) =
      (m.finitePart : Ideal (𝓞 K)) ⊓ (n.finitePart : Ideal (𝓞 K)) := rfl

end Modulus
end NumberField
