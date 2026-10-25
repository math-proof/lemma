/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Instance.NumberTheory.LucasLehmerAcceptableSeed
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_zero_fst {s₁ : ℤ} {q : ℕ} :
    (0 : lucasLehmerSeed_X s₁ q).1 = 0 := rfl

@[simp] theorem lucasLehmerSeed_zero_snd {s₁ : ℤ} {q : ℕ} :
    (0 : lucasLehmerSeed_X s₁ q).2 = 0 := rfl

@[simp] theorem lucasLehmerSeed_add_fst {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) : (x + y).1 = x.1 + y.1 := rfl

@[simp] theorem lucasLehmerSeed_add_snd {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) : (x + y).2 = x.2 + y.2 := rfl

@[simp] theorem lucasLehmerSeed_neg_fst {s₁ : ℤ} {q : ℕ}
    (x : lucasLehmerSeed_X s₁ q) : (-x).1 = -x.1 := rfl

@[simp] theorem lucasLehmerSeed_neg_snd {s₁ : ℤ} {q : ℕ}
    (x : lucasLehmerSeed_X s₁ q) : (-x).2 = -x.2 := rfl

theorem lucasLehmerSeed_X_ext {s₁ : ℤ} {q : ℕ}
    {x y : lucasLehmerSeed_X s₁ q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x
  cases y
  congr

end MetaMathlibExt
