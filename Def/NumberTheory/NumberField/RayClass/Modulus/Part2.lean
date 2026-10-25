/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part3
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
noncomputable def gcd (m n : Modulus K) : Modulus K :=
  ⟨⟨(m.finitePart : Ideal (𝓞 K)) ⊔ (n.finitePart : Ideal (𝓞 K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (by
      intro h
      have hm0 : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
        mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
      exact hm0 (le_antisymm (h ▸ le_sup_left) zero_le))⟩,
    m.infinitePart ∩ n.infinitePart⟩

open Classical in
noncomputable def lcm (m n : Modulus K) : Modulus K :=
  ⟨⟨(m.finitePart : Ideal (𝓞 K)) ⊓ (n.finitePart : Ideal (𝓞 K)),
    mem_nonZeroDivisors_iff_ne_zero.mpr (by
      have h1 : (m.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
        have h := mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
        simpa using h
      have h2 : (n.finitePart : Ideal (𝓞 K)) ≠ ⊥ := by
        have h := mem_nonZeroDivisors_iff_ne_zero.mp n.finitePart.property
        simpa using h
      have h := Ideal.inf_ne_bot_of_ne_bot h1 h2
      simpa using h)⟩,
    m.infinitePart ∪ n.infinitePart⟩

end Modulus
end NumberField
