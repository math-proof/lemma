import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
open StatMech StatMech.FrontierA


/--
[kwRectilinearVector_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_zero_eq :
-- imply
  kwRectilinearVector 0 = 1 := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_zero

/--
[kwRectilinearVector_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_one_eq :
-- imply
  kwRectilinearVector 1 = Complex.I := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_one

/--
[kwRectilinearVector_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_two_eq :
-- imply
  kwRectilinearVector 2 = -1 := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_two

/--
[kwRectilinearVector_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_three_eq :
-- imply
  kwRectilinearVector 3 = -Complex.I := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_three

/--
[kwRectilinearVector_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_ne_zero_eq
  {d : Fin 4} :
-- imply
  kwRectilinearVector d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_ne_zero d

/--
[kwRectilinearVector_arg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_arg_eq
  {d : Fin 4} :
-- imply
  (Complex.arg (kwRectilinearVector d) : Real.Angle) = kwRectilinearAngle d := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_arg d

/--
[kw_angle_coe_eq_of_sub_eq_full_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kw_angle_coe_eq_of_sub_eq_full_turn_eq
  {x y : ℝ}
-- given
  (h : x - y = 2 * Real.pi ∨ x - y = -(2 * Real.pi)) :
-- imply
  (x : Real.Angle) = (y : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.kw_angle_coe_eq_of_sub_eq_full_turn h

/--
[kwRectilinearAngle_succ_sub_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearAngle_succ_sub_toReal_eq
  {d : Fin 4} :
-- imply
  (kwRectilinearAngle (d + 1) - kwRectilinearAngle d).toReal = Real.pi / 2 := by
-- proof
  apply StatMech.FrontierA.kwRectilinearAngle_succ_sub_toReal d

/--
[kwRectilinearAngle_pred_sub_toReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearAngle_pred_sub_toReal_eq
  {d : Fin 4} :
-- imply
  (kwRectilinearAngle (d + 3) - kwRectilinearAngle d).toReal = -(Real.pi / 2) := by
-- proof
  apply StatMech.FrontierA.kwRectilinearAngle_pred_sub_toReal d

/--
[kwAngleTurnPhase_pi_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwAngleTurnPhase_pi_div_two_eq :
-- imply
  Complex.exp ((((Real.pi / 2 : ℝ) : ℂ) * Complex.I) / 2) = ons_turnRoot := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_pi_div_two

/--
[kwAngleTurnPhase_neg_pi_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwAngleTurnPhase_neg_pi_div_two_eq :
-- imply
  Complex.exp ((((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) / 2) = ons_turnRoot⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_neg_pi_div_two

/--
[kwVectorTurnPhase_rectilinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwVectorTurnPhase_rectilinear_eq
  {d e : Fin 4}
-- given
  (hnu : e ≠ d + 2) :
-- imply
  kwVectorTurnPhase (kwRectilinearVector d) (kwRectilinearVector e) = ons_turnW ons_turnRoot d e := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_rectilinear d e hnu

/--
[kwRectilinearVector_phaseProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean)
-/
@[path]
private lemma kwRectilinearVector_phaseProduct_eq_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
-- imply
  (∏ i, kwVectorTurnPhase (kwRectilinearVector (d i)) (kwRectilinearVector (d (i + 1)))) = -1 := by
-- proof
  apply StatMech.FrontierA.kwRectilinearVector_phaseProduct_eq_neg_one d hclosed hsimple hn hnu


-- created on 2026-10-23
