import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.Part4
open Finset StatMech StatMech.Ising


/--
[card_lpReplicaTripleSeamGhostSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma card_lpReplicaTripleSeamGhostSource_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  (lpReplicaTripleSeamGhostSource sites i j k).card = 8 := by
-- proof
  apply StatMech.Ising.card_lpReplicaTripleSeamGhostSource sites hsite hij hik hjk

/--
[lpReplicaCurrentFold_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaCurrentFold_left_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  lpReplicaCurrentFold (.inl (.inl x) : LPReplicaCurrentVertex V) = Sum.inl x := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFold_left x

/--
[lpReplicaCurrentFold_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaCurrentFold_right_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  lpReplicaCurrentFold (.inl (.inr x) : LPReplicaCurrentVertex V) = Sum.inl x := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFold_right x

/--
[lpReplicaCurrentFold_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaCurrentFold_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {b : Bool} :
-- imply
  lpReplicaCurrentFold (.inr b : LPReplicaCurrentVertex V) = Sum.inr () := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFold_ghost b

/--
[lpReplicaCurrentFold_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaCurrentFold_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {x : LPReplicaCurrentVertex V} :
-- imply
  lpReplicaCurrentFold (lpReplicaCurrentReflect x) = lpReplicaCurrentFold x := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFold_reflect x

/--
[lpReplicaCurrentFoldedEdge_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaCurrentFoldedEdge_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  lpReplicaCurrentFoldedEdge G sites (lpReplicaCurrentEdgeReflect G sites e) = lpReplicaCurrentFoldedEdge G sites e := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFoldedEdge_reflect G sites e

/--
[lpReplicaOrbitFourColorSlotEnds_fold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEnds_fold_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Sym2.map lpReplicaCurrentFold (lpReplicaOrbitFourColorSlotEnds G sites q s x) = lpReplicaOrbitFoldedSlotEnds G sites q x := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEnds_fold G sites q s x

/--
[lpReplicaCurrentFoldedEdge_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaCurrentFoldedEdge_seam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i : I}
-- given
  (sites : I -> V)
  (hmem : lpReplicaCurrentSeamEdge sites i ∈ (lpReplicaCurrentGraph G sites).edgeFinset) :
-- imply
  lpReplicaCurrentFoldedEdge G sites ⟨lpReplicaCurrentSeamEdge sites i, hmem⟩ = s(Sum.inl (sites i), Sum.inl (sites i)) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFoldedEdge_seam G sites i hmem

/--
[lpReplicaOrbitFoldedSlotEnds_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaOrbitFoldedSlotEnds_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitFoldedSlotEnds G sites q (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) = lpReplicaCurrentFoldedEdge G sites c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFoldedSlotEnds_copy G sites q m hm L c

/--
[lpReplicaOffdiagDecoratedSource_fullRawSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_fullRawSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) z.1.1.1) Finset.univ = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_fullRawSources G sites q z

/--
[lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) z.1.1.1) (Finset.univ \ {c}) = lpReplicaTripleSeamGhostSource sites i j k := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy G sites q z c hc

/--
[lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (Finset.univ \ {c}).card = 4 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive G sites q hcard z c

/--
[randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {K : Finset E}
-- given
  (ends : E -> Sym2 W)
  (hcard : (StatMech.Sharpness.RandomCurrent.sources ends K).card = 2 * K.card) :
-- imply
  K.biUnion (fun e => (ends e).toFinset) = StatMech.Sharpness.RandomCurrent.sources ends K := by
-- proof
  apply StatMech.Ising.randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul ends K hcard

/--
[randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {K : Finset E}
  {x : W}
-- given
  (ends : E -> Sym2 W)
  (hcard : (StatMech.Sharpness.RandomCurrent.sources ends K).card = 2 * K.card)
  (hx : x ∈ K.biUnion (fun e => (ends e).toFinset)) :
-- imply
  ∃! e, e ∈ K ∧ x ∈ (ends e).toFinset := by
-- proof
  apply StatMech.Ising.randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul ends K hcard hx

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching_eq
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
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites k ∧ let K := Finset.univ \ {c} let E := StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 K.card = 4 ∧ StatMech.Sharpness.RandomCurrent.sources E K = lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧ K.biUnion (fun e => (E e).toFinset) = lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧ ∀ x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k, ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching G sites hsite q hcard z


-- created on 2026-10-23
