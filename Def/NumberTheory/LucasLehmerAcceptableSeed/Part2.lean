/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Instance.NumberTheory.LucasLehmerAcceptableSeed.Part7
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

def lucasLehmerSeed_alpha (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_X s₁ q :=
  ((s₁ : ZMod q) / 2, 1 / 2)

def lucasLehmerSeed_beta (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_X s₁ q :=
  ((s₁ : ZMod q) / 2, -(1 / 2))

end MetaMathlibExt
