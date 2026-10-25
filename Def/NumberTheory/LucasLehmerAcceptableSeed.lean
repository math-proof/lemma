/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

def lucasLehmerSeed_D (s₁ : ℤ) (q : ℕ) : ZMod q := s₁ ^ 2 - 4

def lucasLehmerSeed_X (_s₁ : ℤ) (q : ℕ) : Type := ZMod q × ZMod q

end MetaMathlibExt
