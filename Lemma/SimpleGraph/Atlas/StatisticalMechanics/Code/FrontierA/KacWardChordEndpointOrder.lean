import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrder.Part3
open StatMech StatMech.FrontierA


/--
[kw_halfAngle_two_eq_neg_four_of_odd_full_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kw_halfAngle_two_eq_neg_four_of_odd_full_turn_eq
  {x₁ x₂ y₁ y₂ y₃ y₄ : ℝ}
-- given
  (hturn : x₁ + x₂ - (y₁ + y₂ + y₃ + y₄) = 2 * Real.pi ∨ x₁ + x₂ - (y₁ + y₂ + y₃ + y₄) = -(2 * Real.pi)) :
-- imply
  Complex.exp (((x₁ : ℂ) * Complex.I) / 2) * Complex.exp (((x₂ : ℂ) * Complex.I) / 2) = -(Complex.exp (((y₁ : ℂ) * Complex.I) / 2) * Complex.exp (((y₂ : ℂ) * Complex.I) / 2) * (Complex.exp (((y₃ : ℂ) * Complex.I) / 2) * Complex.exp (((y₄ : ℂ) * Complex.I) / 2))) := by
-- proof
  apply StatMech.FrontierA.kw_halfAngle_two_eq_neg_four_of_odd_full_turn x₁ x₂ y₁ y₂ y₃ y₄ hturn

/--
[kwChordBoundaryTurnDiscrepancy_eq_endpointDefects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kwChordBoundaryTurnDiscrepancy_eq_endpointDefects_eq
  {a b c d chord : ℂ} :
-- imply
  kwChordBoundaryTurnDiscrepancy a b c d chord = kwAntipodalEndpointTurnDefect a b chord + kwAntipodalEndpointTurnDefect c d (-chord) := by
-- proof
  apply StatMech.FrontierA.kwChordBoundaryTurnDiscrepancy_eq_endpointDefects a b c d chord

/--
[kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi_eq
  {a b chord : ℂ}
-- given
  (hchord : chord ≠ 0) :
-- imply
  let defect := ((Complex.arg b : Real.Angle) - (Complex.arg a : Real.Angle)).toReal - ((Complex.arg (-chord) : Real.Angle) - (Complex.arg a : Real.Angle)).toReal - ((Complex.arg b : Real.Angle) - (Complex.arg chord : Real.Angle)).toReal defect = Real.pi ∨ defect = -Real.pi := by
-- proof
  apply StatMech.FrontierA.kw_antipodal_endpoint_turn_defect_eq_pi_or_neg_pi a b chord hchord

/--
[kwAntipodalEndpointTurnDefect_eq_pi_or_neg_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kwAntipodalEndpointTurnDefect_eq_pi_or_neg_pi_eq
  {a b chord : ℂ}
-- given
  (hchord : chord ≠ 0) :
-- imply
  kwAntipodalEndpointTurnDefect a b chord = Real.pi ∨ kwAntipodalEndpointTurnDefect a b chord = -Real.pi := by
-- proof
  apply StatMech.FrontierA.kwAntipodalEndpointTurnDefect_eq_pi_or_neg_pi a b chord hchord

/--
[kwChordBoundaryTurnDiscrepancy_ne_zero_iff_endpointDefects_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kwChordBoundaryTurnDiscrepancy_ne_zero_iff_endpointDefects_eq_eq
  {a b c d chord : ℂ}
-- given
  (hchord : chord ≠ 0) :
-- imply
  kwChordBoundaryTurnDiscrepancy a b c d chord ≠ 0 ↔ kwAntipodalEndpointTurnDefect a b chord = kwAntipodalEndpointTurnDefect c d (-chord) := by
-- proof
  apply StatMech.FrontierA.kwChordBoundaryTurnDiscrepancy_ne_zero_iff_endpointDefects_eq a b c d chord hchord

/--
[kwChordBoundaryTurnDiscrepancy_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kwChordBoundaryTurnDiscrepancy_trichotomy_eq
  {a b c d chord : ℂ}
-- given
  (hchord : chord ≠ 0) :
-- imply
  kwChordBoundaryTurnDiscrepancy a b c d chord = 2 * Real.pi ∨ kwChordBoundaryTurnDiscrepancy a b c d chord = 0 ∨ kwChordBoundaryTurnDiscrepancy a b c d chord = -(2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.kwChordBoundaryTurnDiscrepancy_trichotomy a b c d chord hchord

/--
[kwChordBoundaryTurnDiscrepancy_odd_iff_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kwChordBoundaryTurnDiscrepancy_odd_iff_ne_zero_eq
  {a b c d chord : ℂ}
-- given
  (hchord : chord ≠ 0) :
-- imply
  (kwChordBoundaryTurnDiscrepancy a b c d chord = 2 * Real.pi ∨ kwChordBoundaryTurnDiscrepancy a b c d chord = -(2 * Real.pi)) ↔ kwChordBoundaryTurnDiscrepancy a b c d chord ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwChordBoundaryTurnDiscrepancy_odd_iff_ne_zero a b c d chord hchord

/--
[kwVectorTurnPhase_chord_boundary_of_odd_full_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma kwVectorTurnPhase_chord_boundary_of_odd_full_turn_eq
  {a b c d chord : ℂ}
-- given
  (hturn : kwChordBoundaryTurnDiscrepancy a b c d chord = 2 * Real.pi ∨ kwChordBoundaryTurnDiscrepancy a b c d chord = -(2 * Real.pi)) :
-- imply
  kwVectorTurnPhase a b * kwVectorTurnPhase c d = -(kwVectorTurnPhase a (-chord) * kwVectorTurnPhase (-chord) d * (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b)) := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_chord_boundary_of_odd_full_turn a b c d chord hturn

/--
[KWFiniteSimplePolygon.cleanChordEndpointOddFullTurn_of_endpointOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma cleanChordEndpointOddFullTurn_of_endpointOrder_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 1 ≤ j.val)
  (horder : polygon.CleanChordEndpointOrder j hj) :
-- imply
  polygon.CleanChordEndpointOddFullTurn j hj := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChordEndpointOddFullTurn_of_endpointOrder polygon j hj horder

/--
[KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_of_oddFullTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean)
-/
@[path]
private lemma cleanChordBoundaryPhaseCompatible_of_oddFullTurn_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 1 ≤ j.val)
  (hturn : polygon.CleanChordEndpointOddFullTurn j hj) :
-- imply
  polygon.CleanChordBoundaryPhaseCompatible j hj := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_of_oddFullTurn polygon j hj hturn


-- created on 2026-10-23
