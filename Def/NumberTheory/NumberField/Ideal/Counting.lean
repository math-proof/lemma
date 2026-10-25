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
import Theorem.NumberTheory.NumberField.Ideal.Counting
open scoped NumberField


namespace NumberField

namespace Ideal

variable (K : Type*) [Field K] [NumberField K]

/-- The fiber element over a prime factor; a pure term so projections hold
by `rfl`. -/
noncomputable def fiberMkAux {M : ℕ} (p : ℕ) (hprimep : p.Prime)
    (hpleM : p ≤ M) {P : Ideal (𝓞 K)} (hprime : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    primeFibers K M :=
  ⟨⟨p, hprimep, hpleM⟩, P, hprime, hlies⟩

/-- Injection data: the padded factor list of a bounded ideal. -/
noncomputable def encode (M : ℕ)
    (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}) :
    Fin (Nat.log 2 M) → Option (primeFibers K M) := fun i =>
  if h : i.val < (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length
  then
    have hPmem : (UniqueFactorizationMonoid.normalizedFactors x.1).toList[i.val]'h ∈
        UniqueFactorizationMonoid.normalizedFactors x.1 :=
      Multiset.mem_toList.mp (List.mem_of_getElem rfl)
    have hprops := factor_props K x.2.1 x.2.2 hPmem
    have hex := exists_prime_liesOver K M hprops.1 hprops.2.1 hprops.2.2
    some (fiberMkAux K hex.choose hex.choose_spec.1 hex.choose_spec.2.1
      hprops.1 hex.choose_spec.2.2)
  else none

end Ideal
end NumberField
