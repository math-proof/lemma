/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part4
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

instance lucasLehmerSeed_addGroupWithOne (s₁ : ℤ) (q : ℕ) :
    AddGroupWithOne (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_monoid s₁ q, lucasLehmerSeed_addCommGroup s₁ q,
      lucasLehmerSeed_natCast s₁ q with
    natCast_zero := by
      apply lucasLehmerSeed_X_ext <;> simp
    natCast_succ := fun _ => by
      apply lucasLehmerSeed_X_ext <;> simp
    intCast n := (n, 0)
    intCast_ofNat := fun _ => by
      apply lucasLehmerSeed_X_ext <;> simp
    intCast_negSucc := fun _ => by
      apply lucasLehmerSeed_X_ext <;> simp }

end MetaMathlibExt
