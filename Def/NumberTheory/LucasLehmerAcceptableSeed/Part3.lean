/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part7
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

def lucasLehmerSeed_alphaUnit (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) : (lucasLehmerSeed_X s₁ q)ˣ where
  val := lucasLehmerSeed_alpha s₁ q
  inv := lucasLehmerSeed_beta s₁ q
  val_inv := lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd
  inv_val := lucasLehmerSeed_beta_mul_alpha s₁ q hq_odd

end MetaMathlibExt
