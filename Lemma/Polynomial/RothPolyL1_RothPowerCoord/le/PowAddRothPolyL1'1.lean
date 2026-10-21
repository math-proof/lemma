import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyL1_RothPowerCoordAdd_1.le.MulAddRothPolyL1'1RothPolyL1_RothPowerCoord
import Lemma.Polynomial.RothPolyL1_C.eq.NatAbs
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_powerCoord_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (g : ℤ[X])
  (n : ℕ) :
-- imply
  rothPolyL1 (rothPowerCoord g n) ≤ (rothPolyL1 g + 1) ^ n := by
-- proof
  induction n with
  | zero =>
    rw [rothPowerCoord, show (1 : ℤ[X]) = C 1 by simp, RothPolyL1_C.eq.NatAbs]
    simp
  | succ n ih =>
    calc
      _ ≤ (rothPolyL1 g + 1) * rothPolyL1 (rothPowerCoord g n) :=
        RothPolyL1_RothPowerCoordAdd_1.le.MulAddRothPolyL1'1RothPolyL1_RothPowerCoord g n
      _ ≤ (rothPolyL1 g + 1) * (rothPolyL1 g + 1) ^ n :=
        Nat.mul_le_mul_left _ ih
      _ = (rothPolyL1 g + 1) ^ (n + 1) := by
        rw [pow_succ]
        ac_rfl


-- created on 2026-10-21
