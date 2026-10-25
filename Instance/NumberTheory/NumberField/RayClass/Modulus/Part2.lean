/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/Modulus.lean -/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Theorem.NumberTheory.NumberField.RayClass.Modulus.Part2
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
instance : CommMonoid (Modulus K) where
  one_mul m := by ext <;> simp [Finset.empty_union]
  mul_one m := by ext <;> simp [Finset.union_empty]
  mul_assoc m n p := by ext <;> simp [mul_assoc, Finset.union_assoc]
  mul_comm m n := by ext <;> simp [mul_comm, Finset.union_comm]

end Modulus
end NumberField
