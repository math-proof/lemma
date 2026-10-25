/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/RelativePDerivation.lean -/


import Instance.RingTheory.RelativePDerivation
import Lemma.Int.RelativePDerivation
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
open MetaMathlibExt


-- Tests for C_p at p=2 and p=3, and end-to-end RelativePDerivation into ZMod 1.

-- The integer coefficient really is the quotient claimed in the source formula.
example (p i : ℕ) [Fact p.Prime] (hi : i ≠ 0) (hip : i < p) :
    (p : ℤ) * pDerivationCorrectionCoeff p i = -(Nat.choose p i : ℤ) := by
  unfold pDerivationCorrectionCoeff
  have hq : (p : ℤ) * ((Nat.choose p i : ℤ) / (p : ℤ)) = (Nat.choose p i : ℤ) :=
    Int.mul_ediv_cancel'
      (Int.ofNat_dvd.mpr ((Fact.out : p.Prime).dvd_choose_self hi hip))
  calc
    (p : ℤ) * -((Nat.choose p i : ℤ) / (p : ℤ)) =
        -((p : ℤ) * ((Nat.choose p i : ℤ) / (p : ℤ))) := Int.mul_neg _ _
    _ = -(Nat.choose p i : ℤ) := congrArg Neg.neg hq

-- p = 2 : C_2(x,y) = - x*y  because (x^2+y^2-(x+y)^2)/2 = -xy
-- choose 2 1 = 2, coefficient -1.
example {B : Type*} [CommRing B] (x y : B) : pDerivationCorrection 2 x y = -x * y := by
  have hI : Finset.Ico 1 2 = {1} := by decide
  simp [pDerivationCorrection, hI, pDerivationCorrectionCoeff]

-- p = 3 : C_3(x,y) = - x^2*y - x*y^2 = -x*y*(x+y)
-- choose 3 1 = 3, choose 3 2 = 3, both coefficients -1.
example {B : Type*} [CommRing B] (x y : B) :
    pDerivationCorrection 3 x y = -x ^ 2 * y - x * y ^ 2 := by
  have hI : Finset.Ico 1 3 = {1, 2} := by decide
  simp [pDerivationCorrection, hI, pDerivationCorrectionCoeff]
  ring

-- Alternative form for p=3.
example {B : Type*} [CommRing B] (x y : B) : pDerivationCorrection 3 x y = -x * y * (x + y) := by
  have hI : Finset.Ico 1 3 = {1, 2} := by decide
  simp [pDerivationCorrection, hI, pDerivationCorrectionCoeff]
  ring

