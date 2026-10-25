/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part2
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

instance lucasLehmerSeed_one (s₁ : ℤ) (q : ℕ) : One (lucasLehmerSeed_X s₁ q) where
  one := (1, 0)

end MetaMathlibExt
