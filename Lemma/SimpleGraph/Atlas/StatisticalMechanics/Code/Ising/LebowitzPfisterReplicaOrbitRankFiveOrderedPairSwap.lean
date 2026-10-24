import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagSeamSelector_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaOffdiagSeamSelector_swap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  lpReplicaOffdiagSeamSelector G sites hsite i j hij (ofEdgeFun (lpReplicaCurrentGraph G sites) m) = lpReplicaOffdiagSeamSelector G sites hsite j i hij.symm (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagSeamSelector_swap G sites hsite hij m hsrc

/--
[lpReplicaOffdiagSourceBoundary_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaOffdiagSourceBoundary_swap_eq
  [Fintype V]
  [DecidableEq V]
  {i j : I}
-- given
  (sites : I -> V) :
-- imply
  lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagSourceBoundary_swap sites i j

/--
[lpReplicaAggregateDecoratedSourceSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSwap_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaAggregateDecoratedSourceSwap G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSwap_involutive G sites q

/--
[lpReplicaAggregateDecoratedSourceSwap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSwap_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaAggregateDecoratedSourceSwap G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSwap_injective G sites q

/--
[lpReplicaAggregateDecoratedSourceSwap_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSwap_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedSourceSwap G sites q z ≠ z := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSwap_ne G sites q z

/--
[lpReplicaAggregateDecoratedSourceSwap_canonical_of_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSwap_canonical_of_not_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : ¬ LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q z) :
-- imply
  LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q (lpReplicaAggregateDecoratedSourceSwap G sites q z) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSwap_canonical_of_not G sites q z h

/--
[lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q z) :
-- imply
  ¬ LPReplicaAggregateDecoratedSource.IsCanonicalOrderedPair G sites q (lpReplicaAggregateDecoratedSourceSwap G sites q z) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourceSwap_not_canonical_of_canonical G sites q z h

/--
[lpReplicaAggregateDecoratedSourcePairDecode_code](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourcePairDecode_code_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateDecoratedSource G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedSourcePairDecode G sites q (lpReplicaAggregateDecoratedSourcePairCode G sites q z) = z := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourcePairDecode_code G sites q z

/--
[lpReplicaAggregateDecoratedSourcePairCode_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedSourcePairCode_decode_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x : Fin 2 × LPReplicaAggregateDecoratedSourcePairRepresentative G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedSourcePairCode G sites q (lpReplicaAggregateDecoratedSourcePairDecode G sites q x) = x := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedSourcePairCode_decode G sites q x


-- created on 2026-10-23
