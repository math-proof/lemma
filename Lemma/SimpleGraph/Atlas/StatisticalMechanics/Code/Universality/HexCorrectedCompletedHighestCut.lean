import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut.Part3
open StatMech StatMech.Universality


/--
[hexCSCompletedSplit_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean)
-/
@[path]
private lemma hexCSCompletedSplit_injective_eq
  {T : ℕ}
-- given
  (hT : 1 ≤ T) :
-- imply
  Function.Injective (hexCSCompletedSplit T hT) := by
-- proof
  apply StatMech.Universality.hexCSCompletedSplit_injective T hT

/--
[hexCSCompletedSplit_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean)
-/
@[path]
private lemma hexCSCompletedSplit_length_eq
  {T : ℕ}
  {d : {ts : List ℤ // HexCSNewSideWalk T hT ts}}
-- given
  (hT : 1 ≤ T) :
-- imply
  (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).1.1).endpointNumVertices + (ofTurns hexAWStart 1 (hexCSCompletedSplit T hT d).2.1).endpointNumVertices = (ofTurns hexAWStart 1 d.1).endpointNumVertices + 5 := by
-- proof
  apply StatMech.Universality.hexCSCompletedSplit_length T hT d

/--
[hexCSCompletedTop_tsum_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean)
-/
@[path]
private lemma hexCSCompletedTop_tsum_eq_mass_eq
  {T : ℕ}
-- given
  (hT : 1 ≤ T) :
-- imply
  (∑' b : HexCSCompletedTopWalk T hT, hexEndpointSAWwt hexAWStart 1 hexChiE b.1) = hexCSInfiniteTopMassAtWidth (T + 2) := by
-- proof
  apply StatMech.Universality.hexCSCompletedTop_tsum_eq_mass T hT

/--
[hexCS_completedHighestCut_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean)
-/
@[path]
private lemma hexCS_completedHighestCut_recurrence_eq
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  ∀ T, 1 ≤ T → hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T ≤ (hexChiE⁻¹ ^ 5) * (hexCSInfiniteTopMassAtWidth (T + 2) * hexCSInfiniteTopMassAtWidth (T + 2)) := by
-- proof
  apply StatMech.Universality.hexCS_completedHighestCut_recurrence hwalk

/--
[hexCS_critical_divergence_of_completedHighestCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean)
-/
@[path]
private lemma hexCS_critical_divergence_of_completedHighestCut_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexCS_critical_divergence_of_completedHighestCut hlocal


-- created on 2026-10-23
