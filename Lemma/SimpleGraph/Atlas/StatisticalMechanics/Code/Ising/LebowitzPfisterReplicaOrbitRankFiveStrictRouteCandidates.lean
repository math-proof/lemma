import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates
open StatMech StatMech.Ising


/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {c : Copy (lpReplicaCurrentGraph G sites) (z.toAggregate G sites q).2.2.2.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q (z.toAggregate G sites q))) :
-- imply
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a let K := Finset.univ \ {c} let E := endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 K.card = 4 ∧ StatMech.Sharpness.RandomCurrent.sources E K = lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧ K.biUnion (fun e => (E e).toFinset) = lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧ ∀ x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k, ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_perfectMatching_of_seamCopy G sites hsite q hcard z c hc

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy G sites hsite q z).1.1 = lpReplicaCurrentSeamEdge sites (lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q (z.toAggregate G sites q)) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy_edge G sites hsite q z

/--
[mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : Copy (lpReplicaCurrentGraph G sites) (z.toAggregate G sites q).2.2.2.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  d ∈ lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z ↔ let a := z.toAggregate G sites q let c := lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy G sites hsite q z d ∈ Finset.univ \ {c} ∧ (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉ endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧ (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧ ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag := by
-- proof
  apply StatMech.Ising.mem_lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_iff G sites hsite q z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).Nonempty := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_nonempty G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : Copy (lpReplicaCurrentGraph G sites) (z.toAggregate G sites q).2.2.2.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hd : d ∈ lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z) :
-- imply
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ∃ route : LPReplicaAggregateRankFiveStrictRouteData G sites q a k, route.c = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy G sites hsite q z ∧ route.d = d := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictRouteData_of_candidate G sites hsite q hcard z d hd

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate G sites hsite q hcard z d).c = lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteSeamCopy G sites hsite q z := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_c G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate G sites hsite q hcard z d).d = d.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteDataOfCandidate_d G sites hsite q hcard z d

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  0 < (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_pos G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card ≤ 2 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_le_two G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidates.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card = 1 ∨ (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates_card_eq_one_or_two G sites hsite q hcard z


-- created on 2026-10-23
