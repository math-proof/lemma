import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrderReverse
open StatMech StatMech.FrontierA


/--
[kwVectorTurnPhase_chord_boundary_of_zero_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderReverse.lean)
-/
@[path]
private lemma kwVectorTurnPhase_chord_boundary_of_zero_turn_eq
  {a b c d chord : ℂ}
-- given
  (hturn : kwChordBoundaryTurnDiscrepancy a b c d chord = 0) :
-- imply
  kwVectorTurnPhase a b * kwVectorTurnPhase c d = kwVectorTurnPhase a (-chord) * kwVectorTurnPhase (-chord) d * (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b) := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_chord_boundary_of_zero_turn a b c d chord hturn

/--
[kwChordBoundaryTurnDiscrepancy_ne_zero_of_phaseCompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderReverse.lean)
-/
@[path]
private lemma kwChordBoundaryTurnDiscrepancy_ne_zero_of_phaseCompatible_eq
  {a b c d chord : ℂ}
-- given
  (hcompatible : kwVectorTurnPhase a b * kwVectorTurnPhase c d = -(kwVectorTurnPhase a (-chord) * kwVectorTurnPhase (-chord) d * (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b))) :
-- imply
  kwChordBoundaryTurnDiscrepancy a b c d chord ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwChordBoundaryTurnDiscrepancy_ne_zero_of_phaseCompatible a b c d chord hcompatible

/--
[KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_iff_endpointOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderReverse.lean)
-/
@[path]
private lemma cleanChordBoundaryPhaseCompatible_iff_endpointOrder_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 1 ≤ j.val) :
-- imply
  polygon.CleanChordBoundaryPhaseCompatible j hj ↔ polygon.CleanChordEndpointOrder j hj := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_iff_endpointOrder polygon j hj

/--
[kwVectorPhasePath_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderReverse.lean)
-/
@[path]
private lemma kwVectorPhasePath_ne_zero_eq
  {edges : List ℂ} :
-- imply
  kwVectorPhasePath edges ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_ne_zero edges

/--
[kwVectorPhaseCycle_chord_boundary_of_three_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderReverse.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_chord_boundary_of_three_neg_one_eq
  {p q : List ℂ}
  {chord : ℂ}
-- given
  (hpne : p ≠ [])
  (hqne : q ≠ [])
  (hwhole : kwVectorPhaseCycle (p ++ q) = -1)
  (hp : kwVectorPhaseCycle (p.concat (-chord)) = -1)
  (hq : kwVectorPhaseCycle (q.concat chord) = -1) :
-- imply
  kwVectorTurnPhase (p.getLast hpne) (q.head hqne) * kwVectorTurnPhase (q.getLast hqne) (p.head hpne) = -(kwVectorTurnPhase (p.getLast hpne) (-chord) * kwVectorTurnPhase (-chord) (p.head hpne) * (kwVectorTurnPhase (q.getLast hqne) chord * kwVectorTurnPhase chord (q.head hqne))) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_chord_boundary_of_three_neg_one p q hpne hqne chord hwhole hp hq

/--
[KWFiniteSimplePolygon.cleanChordEndpointOrder_of_three_phaseSigns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrderReverse.lean)
-/
@[path]
private lemma cleanChordEndpointOrder_of_three_phaseSigns_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin n}
-- given
  (hj : 2 ≤ j.val)
  (hclean : polygon.ChordIsClean 0 j)
  (hd : 2 ≤ (-j).val)
  (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j))
  (hwhole : kwVectorPhaseCycle polygon.edgeList = -1)
  (hfirst : kwVectorPhaseCycle (polygon.prefixOfCleanChord j hj hclean).edgeList = -1)
  (hsecond : kwVectorPhaseCycle ((polygon.rotate j).prefixOfCleanChord (-j) hd hcleanRotated).edgeList = -1) :
-- imply
  polygon.CleanChordEndpointOrder j (by omega) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.cleanChordEndpointOrder_of_three_phaseSigns polygon j hj hclean hd hcleanRotated hwhole hfirst hsecond


-- created on 2026-10-23
