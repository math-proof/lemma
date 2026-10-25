import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
open StatMech StatMech.FrontierA


/--
[inhomogeneousEvenSubgraphSum_pos_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorSandwich.lean)
-/
@[path]
private lemma inhomogeneousEvenSubgraphSum_pos_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (weight : Sym2 V -> Real)
  (hweight : forall edge, 0 <= weight edge) :
-- imply
  0 < inhomogeneousEvenSubgraphSum G weight := by
-- proof
  apply StatMech.FrontierA.inhomogeneousEvenSubgraphSum_pos_of_nonneg G weight hweight

/--
[triangularTorusEvenSubgraphSum_log_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorSandwich.lean)
-/
@[path]
private lemma triangularTorusEvenSubgraphSum_log_sandwich_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Real)
  (hweight : forall edge, 0 <= weight edge) :
-- imply
  let sector : Fin 2 -> Fin 2 -> Complex := fun a b => triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) a b Real.log (arfSectorNormMax sector) <= Real.log (inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) /\ Real.log (inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) <= Real.log (arfSectorNormMax sector) + Real.log 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusEvenSubgraphSum_log_sandwich L weight hweight

/--
[triangularTorusEvenSubgraphSum_normalizedLog_gap_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorSandwich.lean)
-/
@[path]
private lemma triangularTorusEvenSubgraphSum_normalizedLog_gap_le_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Real)
  (hweight : forall edge, 0 <= weight edge) :
-- imply
  let sector : Fin 2 -> Fin 2 -> Complex := fun a b => triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) a b let partition := inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight 0 <= (Real.log partition - Real.log (arfSectorNormMax sector)) / (L : Real) ^ 2 /\ (Real.log partition - Real.log (arfSectorNormMax sector)) / (L : Real) ^ 2 <= Real.log 2 / (L : Real) ^ 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusEvenSubgraphSum_normalizedLog_gap_le L weight hweight

/--
[triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorSandwich.lean)
-/
@[path]
private lemma triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero_eq
-- given
  (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
  (hweight : forall L edge, 0 <= weight L edge) :
-- imply
  Filter.Tendsto (fun n : Nat => (Real.log (triangularTorusEvenSubgraphSequence weight n) - Real.log (arfSectorNormMax (triangularTorusSectorSequence weight n))) / (n + 3 : Real) ^ 2) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero weight hweight


-- created on 2026-10-23
