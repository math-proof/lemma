/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part8
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

def lucasLehmerSeed_delta (s₁ : ℤ) (q : ℕ) : lucasLehmerSeed_X s₁ q := (0, 1)

end MetaMathlibExt
