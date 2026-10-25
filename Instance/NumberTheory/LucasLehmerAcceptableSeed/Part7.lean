/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part6
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

instance lucasLehmerSeed_nontrivial (s₁ : ℤ) (q : ℕ) [Fact (1 < q)] :
    Nontrivial (lucasLehmerSeed_X s₁ q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

instance lucasLehmerSeed_fintype (s₁ : ℤ) (q : ℕ) [NeZero q] :
    Fintype (lucasLehmerSeed_X s₁ q) :=
  inferInstanceAs (Fintype (ZMod q × ZMod q))

end MetaMathlibExt
