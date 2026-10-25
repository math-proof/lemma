/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Def.NumberTheory.LucasLehmerAcceptableSeed
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

instance lucasLehmerSeed_inhabited (s₁ : ℤ) (q : ℕ) :
    Inhabited (lucasLehmerSeed_X s₁ q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))

instance lucasLehmerSeed_decidableEq (s₁ : ℤ) (q : ℕ) :
    DecidableEq (lucasLehmerSeed_X s₁ q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))

instance lucasLehmerSeed_addCommGroup (s₁ : ℤ) (q : ℕ) :
    AddCommGroup (lucasLehmerSeed_X s₁ q) :=
  inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

end MetaMathlibExt
