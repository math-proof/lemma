import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.Part4
open Finset StatMech StatMech.Ising StatMech.Ising.LPRankFiveAggregateCounterexample


/--
[sourceSectorStates_unmarked_seam_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean)
-/
@[path]
private lemma sourceSectorStates_unmarked_seam_connected_eq
  {i j : Seam}
  {z : LPRankFiveCounterOrientation × LPRankFiveCounterColoring}
-- given
  (_hij : i ≠ j)
  (_hz : z ∈ sourceSectorStates i j) :
-- imply
  reachable z.1 Finset.univ 6 7 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.sourceSectorStates_unmarked_seam_connected i j _hij z _hz

/--
[card_aggregateSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean)
-/
@[path]
private lemma card_aggregateSource_eq :
-- imply
  Fintype.card AggregateSource = 12 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.card_aggregateSource

/--
[card_aggregateTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean)
-/
@[path]
private lemma card_aggregateTarget_eq :
-- imply
  Fintype.card AggregateTarget = 12 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.card_aggregateTarget

/--
[card_selectedCrossingTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean)
-/
@[path]
private lemma card_selectedCrossingTarget_eq :
-- imply
  Fintype.card SelectedCrossingTarget = 12 := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.card_selectedCrossingTarget

/--
[aggregateSource_card_le_selectedCrossingTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean)
-/
@[path]
private lemma aggregateSource_card_le_selectedCrossingTarget_eq :
-- imply
  Fintype.card AggregateSource ≤ Fintype.card SelectedCrossingTarget := by
-- proof
  apply StatMech.Ising.LPRankFiveAggregateCounterexample.aggregateSource_card_le_selectedCrossingTarget


-- created on 2026-10-23
