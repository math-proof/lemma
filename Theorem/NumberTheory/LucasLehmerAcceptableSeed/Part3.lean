/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LucasLehmer
public import Instance.NumberTheory.LucasLehmerAcceptableSeed.Part3

@[expose] public section

/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_one_fst {s₁ : ℤ} {q : ℕ} :
    (1 : lucasLehmerSeed_X s₁ q).1 = 1 := rfl

@[simp] theorem lucasLehmerSeed_one_snd {s₁ : ℤ} {q : ℕ} :
    (1 : lucasLehmerSeed_X s₁ q).2 = 0 := rfl

end MetaMathlibExt
