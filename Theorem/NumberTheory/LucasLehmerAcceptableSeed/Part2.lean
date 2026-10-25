/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Instance.NumberTheory.LucasLehmerAcceptableSeed.Part2
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_mul_fst {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) :
    (x * y).1 = x.1 * y.1 + lucasLehmerSeed_D s₁ q * x.2 * y.2 := rfl

@[simp] theorem lucasLehmerSeed_mul_snd {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 := rfl

end MetaMathlibExt
