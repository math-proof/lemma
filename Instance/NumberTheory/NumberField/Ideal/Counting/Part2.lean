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
public import Abbrev.NumberTheory.NumberField.Ideal.Counting

@[expose] public section

open scoped NumberField


namespace NumberField

namespace Ideal

variable (K : Type*) [Field K] [NumberField K]

/-- Per-fiber `Fintype`: a nonzero prime of `ℤ` is maximal, so each
`primesOver` set is finite. -/
noncomputable instance fiberFintype (M : ℕ)
    (p : {p : ℕ // p.Prime ∧ p ≤ M}) :
    Fintype ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) := by
  have hcast : ((p.1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.1.ne_zero
  have hprime : (Ideal.span ({(p.1 : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp p.2.1)
  have hP0 : Ideal.span ({(p.1 : ℤ)} : Set ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hcast
  have hmax : (Ideal.span ({(p.1 : ℤ)} : Set ℤ)).IsMaximal :=
    hprime.isMaximal hP0
  infer_instance

/-- `Fintype` for the rational primes bounded by `M`. -/
noncomputable instance instFintypePrimeBounds (M : ℕ) :
    Fintype {p : ℕ // p.Prime ∧ p ≤ M} := by
  have hfin : {p : ℕ | p.Prime ∧ p ≤ M}.Finite :=
    (Finset.range (M + 1)).finite_toSet.subset fun p hp =>
      Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hp.2))
  exact hfin.fintype

noncomputable instance instFintypePrimeFibers (M : ℕ) :
    Fintype (primeFibers K M) := by
  infer_instance

end Ideal
end NumberField
