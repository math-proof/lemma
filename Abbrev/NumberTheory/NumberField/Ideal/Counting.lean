/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Instance.NumberTheory.NumberField.Ideal.Counting
open scoped NumberField


namespace NumberField

namespace Ideal

variable (K : Type*) [Field K] [NumberField K]

/-- Prime ideals of `𝓞 K` lying above rational primes `p ≤ M`, bundled by `p`. -/
abbrev primeFibers (M : ℕ) :=
  (p : {p : ℕ // p.Prime ∧ p ≤ M}) ×
    ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K))

end Ideal
end NumberField
