import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
open StatMech StatMech.FrontierA


/--
[kwAngleTurnPhase_mul_of_sign_or_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardInteriorSideSplice.lean)
-/
@[path]
private lemma kwAngleTurnPhase_mul_of_sign_or_outer_eq
  {a b c : Real.Angle}
-- given
  (hab : b - a ≠ (Real.pi : Real.Angle))
  (hbc : c - b ≠ (Real.pi : Real.Angle))
  (hsign : (b - a).sign ≠ (c - b).sign ∨ (b - a).sign = (c - a).sign) :
-- imply
  kwAngleTurnPhase a b * kwAngleTurnPhase b c = kwAngleTurnPhase a c := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_mul_of_sign_or_outer a b c hab hbc hsign

/--
[kwAngleTurnPhase_mul_eq_neg_of_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardInteriorSideSplice.lean)
-/
@[path]
private lemma kwAngleTurnPhase_mul_eq_neg_of_wrap_eq
  {a b c : Real.Angle}
-- given
  (hab : b - a ≠ (Real.pi : Real.Angle))
  (hbc : c - b ≠ (Real.pi : Real.Angle))
  (hac : c - a ≠ (Real.pi : Real.Angle))
  (hsame : (b - a).sign = (c - b).sign)
  (hwrap : (b - a).sign ≠ (c - a).sign) :
-- imply
  kwAngleTurnPhase a b * kwAngleTurnPhase b c = -kwAngleTurnPhase a c := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_mul_eq_neg_of_wrap a b c hab hbc hac hsame hwrap

/--
[kwAngleTurnPhase_ear_splice_of_interiorSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardInteriorSideSplice.lean)
-/
@[path]
private lemma kwAngleTurnPhase_ear_splice_of_interiorSides_eq
  {p a b q : ℂ}
-- given
  (hp : p ≠ 0)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hq : q ≠ 0)
  (hpA : kwComplexCross p a ≠ 0)
  (hAB : kwComplexCross a b ≠ 0)
  (hBq : kwComplexCross b q ≠ 0)
  (hleft : (0 < kwComplexCross a b ∧ 0 < kwComplexCross p (a + b)) ∨ (kwComplexCross a b < 0 ∧ kwComplexCross p (a + b) < 0))
  (hright : (0 < kwComplexCross a b ∧ 0 < kwComplexCross (a + b) q) ∨ (kwComplexCross a b < 0 ∧ kwComplexCross (a + b) q < 0)) :
-- imply
  kwAngleTurnPhase (Complex.arg p : Real.Angle) (Complex.arg a : Real.Angle) * kwAngleTurnPhase (Complex.arg a : Real.Angle) (Complex.arg b : Real.Angle) * kwAngleTurnPhase (Complex.arg b : Real.Angle) (Complex.arg q : Real.Angle) = kwAngleTurnPhase (Complex.arg p : Real.Angle) (Complex.arg (a + b) : Real.Angle) * kwAngleTurnPhase (Complex.arg (a + b) : Real.Angle) (Complex.arg q : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_ear_splice_of_interiorSides p a b q hp ha hb hq hpA hAB hBq hleft hright


-- created on 2026-10-23
