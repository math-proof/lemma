import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyL1Mul.le.MulRothSPolyL1
import Lemma.Polynomial.RothPolyL1_C.eq.NatAbs
import Lemma.Polynomial.RothPolyL1X.eq.One
import Lemma.Polynomial.RothPolyL1_Sub.le.AddRothSPolyL1
import Lemma.Polynomial.NatAbsCoeff.le.RothPolyL1
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


private lemma rothPolyL1_powerCoord_succ_le
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

private lemma rothPolyL1_powerCoord_le
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
          rothPolyL1_powerCoord_succ_le g n
        _ ≤ (rothPolyL1 g + 1) * (rothPolyL1 g + 1) ^ n :=
          Nat.mul_le_mul_left _ ih
        _ = (rothPolyL1 g + 1) ^ (n + 1) := by
          rw [pow_succ]
          ac_rfl

/--
[rothScaledPowerCoord_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {S n : ℕ}
-- given
  (hn : n ≤ S) :
-- imply
  rothPolyL1 (rothScaledPowerCoord α S n) ≤ rothCoordinateBase α ^ S := by
-- proof
  let a := (rothIntPolynomial α).leadingCoeff
  let g := rothIntegralPolynomial α
  let B := rothCoordinateBase α
  have ha : a.natAbs ≤ B := le_max_left _ _
  have hg : rothPolyL1 g + 1 ≤ B := le_max_right _ _
  calc
    _ ≤ rothPolyL1 (C (a ^ (S - n))) * rothPolyL1 (rothPowerCoord g n) :=
      RothPolyL1Mul.le.MulRothSPolyL1 _ _
    _ = a.natAbs ^ (S - n) * rothPolyL1 (rothPowerCoord g n) := by
      rw [RothPolyL1_C.eq.NatAbs, Int.natAbs_pow]
    _ ≤ a.natAbs ^ (S - n) * (rothPolyL1 g + 1) ^ n := by
      gcongr
      exact rothPolyL1_powerCoord_le g n
    _ ≤ B ^ (S - n) * B ^ n := by
      gcongr
    _ = B ^ S := by
      rw [← pow_add, Nat.sub_add_cancel hn]


-- created on 2026-10-21
