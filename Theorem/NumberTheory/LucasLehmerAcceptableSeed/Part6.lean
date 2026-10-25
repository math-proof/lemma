/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Instance.NumberTheory.LucasLehmerAcceptableSeed.Part6
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_coeZMod_fst {s₁ : ℤ} {q : ℕ} (z : ZMod q) :
    (z : lucasLehmerSeed_X s₁ q).1 = z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast]
  rfl

@[simp] theorem lucasLehmerSeed_coeZMod_snd {s₁ : ℤ} {q : ℕ} (z : ZMod q) :
    (z : lucasLehmerSeed_X s₁ q).2 = 0 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast]
  rfl

end MetaMathlibExt
