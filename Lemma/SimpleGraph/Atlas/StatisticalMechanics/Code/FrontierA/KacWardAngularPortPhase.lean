import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase.Part4
open StatMech StatMech.FrontierA


/--
[kwAngularUnit_chord_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwAngularUnit_chord_of_lt_eq
  {a b : ℝ}
-- given
  (hab : a < b) :
-- imply
  kwAngularUnit b - kwAngularUnit a = ((2 * Real.sin ((b - a) / 2) : ℝ) : ℂ) * kwAngularUnit ((a + b) / 2 + Real.pi / 2) := by
-- proof
  apply StatMech.FrontierA.kwAngularUnit_chord_of_lt hab

/--
[kwAngularUnit_chord_of_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwAngularUnit_chord_of_gt_eq
  {a b : ℝ}
-- given
  (hba : b < a) :
-- imply
  kwAngularUnit b - kwAngularUnit a = ((2 * Real.sin ((a - b) / 2) : ℝ) : ℂ) * kwAngularUnit ((a + b) / 2 - Real.pi / 2) := by
-- proof
  apply StatMech.FrontierA.kwAngularUnit_chord_of_gt hba

/--
[KWAngularPortRadiusData.realizedDartVector_pos_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma realizedDartVector_pos_raw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart} :
-- imply
  ∃ c : ℝ, 0 < c ∧ (data.toStraightLineEmbedding.vertex d.snd - data.toStraightLineEmbedding.vertex d.fst) = (c : ℂ) * kwAngularUnit (data.rawDartDirection d) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.realizedDartVector_pos_raw data d

/--
[kwAngularUnit_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwAngularUnit_ne_zero_eq
  {a : ℝ} :
-- imply
  kwAngularUnit a ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwAngularUnit_ne_zero a

/--
[KWAngularPortRadiusData.realizedTurnPhase_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma realizedTurnPhase_eq_raw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d e : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart} :
-- imply
  data.toStraightLineEmbedding.turnPhase d e = kwAngleTurnPhase (data.rawDartDirection d : Real.Angle) (data.rawDartDirection e : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.realizedTurnPhase_eq_raw data d e

/--
[kwRawDirectionRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwRawDirectionRoot_ne_zero_eq
  {a : ℝ} :
-- imply
  kwRawDirectionRoot a ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwRawDirectionRoot_ne_zero a

/--
[kwAngleTurnPhase_coe_eq_rootRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwAngleTurnPhase_coe_eq_rootRatio_eq
  {a b : ℝ}
-- given
  (hlower : -Real.pi < b - a)
  (hupper : b - a ≤ Real.pi) :
-- imply
  kwAngleTurnPhase (a : Real.Angle) (b : Real.Angle) = (kwRawDirectionRoot a)⁻¹ * kwRawDirectionRoot b := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_coe_eq_rootRatio a b hlower hupper

/--
[kwRawDirectionRoot_add_pi_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwRawDirectionRoot_add_pi_inv_eq
  {a : ℝ} :
-- imply
  (kwRawDirectionRoot (a + Real.pi))⁻¹ = -Complex.I * (kwRawDirectionRoot a)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwRawDirectionRoot_add_pi_inv a

/--
[kwRawDirectionRoot_sub_pi_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwRawDirectionRoot_sub_pi_inv_eq
  {a : ℝ} :
-- imply
  (kwRawDirectionRoot (a - Real.pi))⁻¹ = Complex.I * (kwRawDirectionRoot a)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwRawDirectionRoot_sub_pi_inv a

/--
[kwPortAngleRoot_eq_rawDirectionRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma kwPortAngleRoot_eq_rawDirectionRoot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p : KWDartPort G} :
-- imply
  kwPortAngleRoot embedding p = kwRawDirectionRoot (embedding.dartAngle (kwDartOfPort G p)).toReal := by
-- proof
  apply StatMech.FrontierA.kwPortAngleRoot_eq_rawDirectionRoot embedding p

/--
[KWAngularPortRadiusData.phaseGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma phaseGauge_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart} :
-- imply
  data.phaseGauge d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.phaseGauge_ne_zero data d

/--
[KWAngularPortRadiusData.realizedTurnPhase_eq_phaseGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean)
-/
@[path]
private lemma realizedTurnPhase_eq_phaseGauge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d e : (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  data.toStraightLineEmbedding.turnPhase d e = kwPhaseGauge data.phaseGauge (kwAngularSplitPhase embedding) d e := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.realizedTurnPhase_eq_phaseGauge data d e hconnect hne


-- created on 2026-10-23
