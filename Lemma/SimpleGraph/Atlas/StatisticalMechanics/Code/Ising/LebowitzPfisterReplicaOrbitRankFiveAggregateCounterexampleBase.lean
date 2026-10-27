import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase
open Finset StatMech StatMech.Ising StatMech.Ising.LPRankFiveAggregateCounterexample


/--
[sources_eq_sectorBoundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma sources_eq_sectorBoundary_iff_eq
  {i j : Seam}
  {o : LPRankFiveCounterOrientation}
  {K : Finset LPRankFiveCounterSlot} :
-- imply
  LPRankFiveCounterexample.sources o K = seam i ∆ seam j ∆ ghosts ↔ o ∈ sectorOrientations i j ∧ K = Finset.univ := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.sources_eq_sectorBoundary_iff i j o K

/--
[sources_eq_empty_of_mem_sectorOrientations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma sources_eq_empty_of_mem_sectorOrientations_eq
  {i j : Seam}
  {o : LPRankFiveCounterOrientation}
  {K : Finset LPRankFiveCounterSlot}
-- given
  (ho : o ∈ sectorOrientations i j)
  (hK : LPRankFiveCounterexample.sources o K = ∅) :
-- imply
  K = ∅ := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.sources_eq_empty_of_mem_sectorOrientations i j o ho K hK

/--
[sources_eq_seam_iff_of_mem_sectorOrientations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma sources_eq_seam_iff_of_mem_sectorOrientations_eq
  {i j k : Seam}
  {o : LPRankFiveCounterOrientation}
  {K : Finset LPRankFiveCounterSlot}
-- given
  (ho : o ∈ sectorOrientations i j) :
-- imply
  LPRankFiveCounterexample.sources o K = seam k ↔ k = 2 ∧ K = {4} := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.sources_eq_seam_iff_of_mem_sectorOrientations i j k o ho K

/--
[saturated_pattern_iff_sectorOrientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma saturated_pattern_iff_sectorOrientation_eq
  {i j : Seam}
  {o : LPRankFiveCounterOrientation}
-- given
  (hij : i ≠ j) :
-- imply
  pattern o ∅ (seam i ∆ seam j ∆ ghosts) saturatedColoring ↔ o ∈ sectorOrientations i j := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.saturated_pattern_iff_sectorOrientation i j hij o

/--
[target_pattern_iff_sectorOrientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma target_pattern_iff_sectorOrientation_eq
  {j : Seam}
  {o : LPRankFiveCounterOrientation} :
-- imply
  pattern o (seam 2) (seam j ∆ ghosts) targetColoring ↔ o ∈ sectorOrientations 2 j := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.target_pattern_iff_sectorOrientation j o

/--
[eq_saturatedColoring_of_colorClass_two_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma eq_saturatedColoring_of_colorClass_two_eq_univ_eq
  {c : LPRankFiveCounterColoring}
-- given
  (hc : colorClass c 2 = Finset.univ) :
-- imply
  c = saturatedColoring := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.eq_saturatedColoring_of_colorClass_two_eq_univ c hc

/--
[eq_targetColoring_of_colorClasses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma eq_targetColoring_of_colorClasses_eq
  {c : LPRankFiveCounterColoring}
-- given
  (hzero : colorClass c 0 = {4})
  (hunion : colorClass c 0 ∪ colorClass c 2 = Finset.univ) :
-- imply
  c = targetColoring := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.eq_targetColoring_of_colorClasses c hzero hunion

/--
[mem_sourceSectorStates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma mem_sourceSectorStates_iff_eq
  {i j : Seam}
  {z : LPRankFiveCounterOrientation × LPRankFiveCounterColoring}
-- given
  (hij : i ≠ j) :
-- imply
  z ∈ sourceSectorStates i j ↔ z.1 ∈ sectorOrientations i j ∧ z.2 = saturatedColoring := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.mem_sourceSectorStates_iff i j hij z

/--
[mem_targetSectorStates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma mem_targetSectorStates_iff_eq
  {i j : Seam}
  {z : LPRankFiveCounterOrientation × LPRankFiveCounterColoring} :
-- imply
  z ∈ targetSectorStates i j ↔ i = 2 ∧ z.1 ∈ sectorOrientations i j ∧ z.2 = targetColoring := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.mem_targetSectorStates_iff i j z

/--
[sectorOrientations_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma sectorOrientations_card_eq
  {i j : Seam} :
-- imply
  (sectorOrientations i j).card = 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.sectorOrientations_card i j

/--
[sourceSectorStates_card_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma sourceSectorStates_card_of_ne_eq
  {i j : Seam}
-- given
  (hij : i ≠ j) :
-- imply
  (sourceSectorStates i j).card = 2 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.sourceSectorStates_card_of_ne i j hij

/--
[targetSectorStates_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean)
-/
@[path]
private lemma targetSectorStates_card_eq
  {i j : Seam} :
-- imply
  (targetSectorStates i j).card = if i = 2 then 2 else 0 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.targetSectorStates_card i j


-- created on 2026-10-23
