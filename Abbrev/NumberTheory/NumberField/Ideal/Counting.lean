/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean -/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Instance.NumberTheory.NumberField.Ideal.Counting
@[expose] public section

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
