/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Instance.NumberTheory.NumberField.RayClass.Modulus.Part3
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

@[simp] theorem dvd_unfold (m n : Modulus K) :
    (m ∣ n) ↔ (n.finitePart : Ideal (𝓞 K)) ≤ (m.finitePart : Ideal (𝓞 K)) ∧
      (↑m.infinitePart : Set (RealPlace K)) ⊆ ↑n.infinitePart := Iff.rfl

end Modulus
end NumberField
