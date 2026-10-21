import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyL1_Sub.le.AddRothSPolyL1
import Lemma.Polynomial.RothPolyL1Mul.le.MulRothSPolyL1
import Lemma.Polynomial.RothPolyL1X.eq.One
import Lemma.Polynomial.RothPolyL1_C.eq.NatAbs
import Lemma.Polynomial.NatAbsCoeff.le.RothPolyL1
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_powerCoord_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (g : ℤ[X])
  (n : ℕ) :
-- imply
  rothPolyL1 (rothPowerCoord g (n + 1)) ≤
    (rothPolyL1 g + 1) * rothPolyL1 (rothPowerCoord g n) := by
-- proof
  let u := rothPowerCoord g n
  let c := u.coeff (g.natDegree - 1)
  rw [rothPowerCoord]
  calc
    _ ≤ rothPolyL1 (X * u) + rothPolyL1 (C c * g) :=
      RothPolyL1_Sub.le.AddRothSPolyL1 _ _
    _ ≤ rothPolyL1 X * rothPolyL1 u + rothPolyL1 (C c) * rothPolyL1 g :=
      Nat.add_le_add (RothPolyL1Mul.le.MulRothSPolyL1 _ _)
        (RothPolyL1Mul.le.MulRothSPolyL1 _ _)
    _ = rothPolyL1 u + c.natAbs * rothPolyL1 g := by
      rw [RothPolyL1X.eq.One, RothPolyL1_C.eq.NatAbs, one_mul]
    _ ≤ rothPolyL1 u + rothPolyL1 u * rothPolyL1 g :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_right (rothPolyL1 g) (NatAbsCoeff.le.RothPolyL1 u _)) _
    _ = (rothPolyL1 g + 1) * rothPolyL1 u := by
      rw [add_mul, one_mul]
      ac_rfl


-- created on 2026-10-21
