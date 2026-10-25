import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.Part2
open StatMech StatMech.Ising


/--
[lpReplicaCurrentSeamEdge_toFinset_eq_matchingSeamSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaCurrentSeamEdge_toFinset_eq_matchingSeamSource_eq
  [Fintype V]
  [DecidableEq V]
  {k : I}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentSeamEdge sites k).toFinset = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentSeamEdge_toFinset_eq_matchingSeamSource sites k

/--
[lpReplicaCurrentCopies_singletonFalse_false_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_singletonFalse_false_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaSingletonFalseRowTag c) false false = {c} := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_singletonFalse_false_false G sites m c

/--
[lpReplicaCurrentCopies_singletonFalse_false_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_singletonFalse_false_true_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaSingletonFalseRowTag c) false true = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_singletonFalse_false_true G sites m c

/--
[lpReplicaCurrentCopies_singletonFalse_true_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_singletonFalse_true_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaSingletonFalseRowTag c) true false = Finset.univ \ {c} := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_singletonFalse_true_false G sites m c

/--
[lpReplicaCurrentCopies_singletonFalse_true_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_singletonFalse_true_true_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaSingletonFalseRowTag c) true true = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_singletonFalse_true_true G sites m c

/--
[lpReplicaRowCopies_singletonFalse_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaRowCopies_singletonFalse_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaRowCopies G sites m (lpReplicaSingletonFalseRowTag c) false = {c} := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_singletonFalse_false G sites m c

/--
[lpReplicaRowCopies_singletonFalse_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean)
-/
@[path]
private lemma lpReplicaRowCopies_singletonFalse_true_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaRowCopies G sites m (lpReplicaSingletonFalseRowTag c) true = Finset.univ \ {c} := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_singletonFalse_true G sites m c


-- created on 2026-10-23
