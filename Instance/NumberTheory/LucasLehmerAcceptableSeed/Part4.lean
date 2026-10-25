/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part3
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

instance lucasLehmerSeed_monoid (s₁ : ℤ) (q : ℕ) :
    Monoid (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_mul s₁ q, lucasLehmerSeed_one s₁ q with
    mul_assoc := fun x y z => by
      apply lucasLehmerSeed_X_ext <;> simp [lucasLehmerSeed_D] <;> ring
    one_mul := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp
    mul_one := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp }

instance lucasLehmerSeed_natCast (s₁ : ℤ) (q : ℕ) :
    NatCast (lucasLehmerSeed_X s₁ q) where
  natCast n := (n, 0)

end MetaMathlibExt
