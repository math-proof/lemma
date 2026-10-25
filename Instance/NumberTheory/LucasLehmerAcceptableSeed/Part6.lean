/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part5
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

instance lucasLehmerSeed_ring (s₁ : ℤ) (q : ℕ) : Ring (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_addGroupWithOne s₁ q, lucasLehmerSeed_addCommGroup s₁ q,
      lucasLehmerSeed_monoid s₁ q with
    left_distrib := fun x y z => by
      apply lucasLehmerSeed_X_ext <;> simp <;> ring
    right_distrib := fun x y z => by
      apply lucasLehmerSeed_X_ext <;> simp <;> ring
    mul_zero := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp
    zero_mul := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp }

instance lucasLehmerSeed_commRing (s₁ : ℤ) (q : ℕ) :
    CommRing (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_ring s₁ q with
    mul_comm := fun x y => by
      apply lucasLehmerSeed_X_ext <;> simp <;> ring }

instance lucasLehmerSeed_charP (s₁ : ℤ) (q : ℕ) :
    CharP (lucasLehmerSeed_X s₁ q) q where
  cast_eq_zero_iff x := by
    convert! ZMod.natCast_eq_zero_iff x q
    exact ⟨congr_arg Prod.fst, fun hx => lucasLehmerSeed_X_ext hx (by simp)⟩

instance lucasLehmerSeed_coeZMod (s₁ : ℤ) (q : ℕ) :
    Coe (ZMod q) (lucasLehmerSeed_X s₁ q) where
  coe := ZMod.castHom dvd_rfl (lucasLehmerSeed_X s₁ q)

end MetaMathlibExt
