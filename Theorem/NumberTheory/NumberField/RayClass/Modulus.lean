/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Structure.NumberTheory.NumberField.RayClass.Modulus
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

@[simp] theorem mk_finitePart (a : (Ideal (𝓞 K))⁰) (b : Finset (RealPlace K)) :
    (⟨a, b⟩ : Modulus K).finitePart = a := rfl

@[simp] theorem mk_infinitePart (a : (Ideal (𝓞 K))⁰) (b : Finset (RealPlace K)) :
    (⟨a, b⟩ : Modulus K).infinitePart = b := rfl

end Modulus
end NumberField
