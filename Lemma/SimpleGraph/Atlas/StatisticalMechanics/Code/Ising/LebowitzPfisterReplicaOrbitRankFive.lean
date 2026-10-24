import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive
open Finset StatMech StatMech.Ising


/--
[randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {c : ι}
-- given
  (ends : ι -> Sym2 W)
  (hdiag : ¬ (ends c).IsDiag) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends {c} = (ends c).toFinset := by
-- proof
  apply StatMech.Ising.randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag ends c hdiag

/--
[exists_mem_ends_of_connK_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma exists_mem_ends_of_connK_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {S : Finset ι}
  {a b : W}
-- given
  (ends : ι -> Sym2 W)
  (hab : a ≠ b)
  (hconn : StatMech.Sharpness.RandomCurrent.connK ends S a b) :
-- imply
  ∃ e ∈ S, a ∈ ends e := by
-- proof
  apply StatMech.Ising.exists_mem_ends_of_connK_of_ne ends S hab hconn

/--
[randomCurrent_connK_insert_parallel_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma randomCurrent_connK_insert_parallel_iff_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {c e : ι}
  {a b : W}
-- given
  (ends : ι -> Sym2 W)
  (he : e ∈ K)
  (hparallel : ends c = ends e) :
-- imply
  StatMech.Sharpness.RandomCurrent.connK ends (insert c K) a b ↔ StatMech.Sharpness.RandomCurrent.connK ends K a b := by
-- proof
  apply StatMech.Ising.randomCurrent_connK_insert_parallel_iff ends K c e he hparallel a b

/--
[lpReplica_seam_union_parallelCopies_ghost_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplica_seam_union_parallelCopies_ghost_disconnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i : I}
  {c e0 : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
  {C : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i)
  (hsame : ∀ e ∈ C, e.1.1 = e0.1.1) :
-- imply
  ¬ StatMech.Sharpness.RandomCurrent.connK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) ({c} ∪ C) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplica_seam_union_parallelCopies_ghost_disconnected G sites i m c e0 C hc hsame

/--
[lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaToggleRows G sites m (Finset.univ \ {c}) (lpReplicaSwapRowsTag tag) = lpReplicaToggleRows G sites m {c} tag := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag G sites m tag c

/--
[lpReplicaRowGate_compl_singleton_currentSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaRowGate_compl_singleton_currentSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m B ∅ tag)
  (hcurrent : (tag c).2 = false) :
-- imply
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m let P := Finset.univ \ {c} StatMech.Sharpness.RandomCurrent.sources E (P.filter fun a => (tag a).2 = false) = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} ∧ StatMech.Sharpness.RandomCurrent.sources E (P.filter fun a => (tag a).2 = true) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_compl_singleton_currentSources G sites m B tag hgate c hcurrent

/--
[lpReplicaOffdiagDecoratedSource_rank_five_active_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_active_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false (K.card = 3 ∧ (Finset.univ \ K).card = 2 ∧ StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) z.1.1.1) (Finset.univ \ K) = ∅) ∨ K = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_active_card G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ) :
-- imply
  ∀ c, (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (true, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies G sites hsite hij q hcard z hsat

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ G sites hsite hij q hcard z hsat

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z w : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hsatZ : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ)
  (hsatW : lpReplicaCurrentCopies G sites w.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q w).1 true false = Finset.univ)
  (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) :
-- imply
  z = w := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq G sites hsite hij q hcard z w hsatZ hsatW htrace

/--
[lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false ∀ c ∈ Finset.univ \ K, ∀ e ∈ Finset.univ \ K, d.1 c = d.1 e := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false ∀ c ∈ Finset.univ \ K, ∀ e ∈ Finset.univ \ K, c.1.1 = e.1.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagDecoratedSource_rank_five_complement_is_tagClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_complement_is_tagClass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false ∃ row current, (row, current) ≠ (true, false) ∧ lpReplicaCurrentCopies G sites z.1.1.1 d.1 row current = Finset.univ \ K := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_complement_is_tagClass G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false)) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) = lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots G sites hsite hij q hcard z hthree c hcC hctag

/--
[lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false)) :
-- imply
  (lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)).card = 3 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three G sites hsite hij q hcard z hthree c hcC hctag

/--
[lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c e : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false))
  (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
-- imply
  lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 e) = e.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive G sites hsite hij q hcard z hthree c e hcC hctag heC

/--
[lpReplica_threeCopyOffdiag_endpointSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplica_threeCopyOffdiag_endpointSupport_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hKcard : K.card = 3)
  (hsource : StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m (K.biUnion fun c => (E c).toFinset) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplica_threeCopyOffdiag_endpointSupport G sites hsite hij m K hKcard hsource

/--
[lpReplica_threeCopyOffdiag_edge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplica_threeCopyOffdiag_edge_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hKcard : K.card = 3)
  (hsource : StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  Set.InjOn (fun c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m => c.1.1) K := by
-- proof
  apply StatMech.Ising.lpReplica_threeCopyOffdiag_edge_injective G sites hsite hij m K hKcard hsource

/--
[lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c0 : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hc0C : c0 ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hc0tag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c0 = (false, false)) :
-- imply
  Set.InjOn (lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active G sites hsite hij q hcard z hthree c0 hc0C hc0tag

/--
[lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c0 : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hc0C : c0 ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hc0tag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c0 = (false, false)) :
-- imply
  Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∈ lpReplicaEligibleInactivePairs (lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible G sites hsite hij q hcard z hthree c0 hc0C hc0tag

/--
[mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive G sites i j q u ↔ z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u ∧ LPReplicaOffdiagDecoratedSource.IsErasedRankFive G sites i j q z := by
-- proof
  apply StatMech.Ising.mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive G sites i j q u z

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive G sites i j q u).card ≤ (lpReplicaEligibleInactivePairs (lpReplicaOrbitFourColorSlotEdge G sites q u)).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive G sites i j q u).card ≤ 3 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three G sites hsite hij q hcard u

/--
[mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive G sites i j q u ↔ z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u ∧ LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive G sites i j q z := by
-- proof
  apply StatMech.Ising.mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive G sites i j q u z

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive G sites i j q u).card ≤ 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_erased_union_saturated_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_erased_union_saturated_card_le_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive G sites i j q u).card ≤ 4 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_erased_union_saturated_card_le_four G sites hsite hij q hcard u

/--
[lpReplica_threeCopyOffdiag_exists_seamCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplica_threeCopyOffdiag_exists_seamCopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hKcard : K.card = 3)
  (hsource : StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  (∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨ ∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
-- proof
  apply StatMech.Ising.lpReplica_threeCopyOffdiag_exists_seamCopy G sites hsite hij m K hKcard hsource

/--
[lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false (∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨ ∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
-- imply
  ∃ s : LPReplicaBalancedSelector G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ HEq s.selector (Finset.univ \ {c}) ∧ @HEq (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag) (lpReplicaToggleRows G sites s.profile s.selector s.tag) (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag) (lpReplicaToggleRows G sites z.1.1.1 {c} (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) ∧ ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inl y)).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∧ y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites i j q s := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam G sites hsite hij q hcard z hthree c hcK hc

/--
[lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {k c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hck : c.1.1 = k.1.1)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false)) :
-- imply
  ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inl y)).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive G sites hsite hij q hcard z hthree k c hkK hk hcC hck hctag

/--
[lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {k c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hk : k.1.1 = lpReplicaCurrentSeamEdge sites j)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hck : c.1.1 = k.1.1)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false)) :
-- imply
  ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inr y)).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive G sites hsite hij q hcard z hthree k c hkK hk hcC hck hctag

/--
[lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites j) :
-- imply
  ∃ s : LPReplicaBalancedSelector G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ HEq s.selector (Finset.univ \ {c}) ∧ @HEq (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag) (lpReplicaToggleRows G sites s.profile s.selector s.tag) (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag) (lpReplicaToggleRows G sites z.1.1.1 {c} (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) ∧ ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inr y)).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∧ ∃ s' : LPReplicaBalancedSelector G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites j i q s' ∧ s'.profile = s.profile ∧ HEq s'.selector s.selector ∧ HEq s'.tag s.tag := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam G sites hsite hij q hcard z hthree c hcK hc

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
-- imply
  ∃ y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q, LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inl y)).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam G sites q z hsat c hc

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ)
  (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagBalancedOutput G sites i j q y ∧ lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y = lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z ∧ (lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2).card = 4 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam G sites hsite hij q hcard z hsat c hc

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {cut : LPReplicaCoupledPairedCut G sites z.1.1.1 (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z).1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ) :
-- imply
  cut.half = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty G sites i j q z hsat cut

/--
[lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_doubledHalf_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_doubledHalf_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {cut : LPReplicaCoupledPairedCut G sites z.1.1.1 (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) (lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z).1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsat : lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false = Finset.univ) :
-- imply
  cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_doubledHalf_eq_empty G sites i j q z hsat cut

/--
[lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  ∃ (y : LPReplicaOffdiagDecoratedTarget G sites i j q) (c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1), LPReplicaOffdiagBalancedOutput G sites i j q y ∧ (c.1.1 = lpReplicaCurrentSeamEdge sites i ∨ c.1.1 = lpReplicaCurrentSeamEdge sites j) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three G sites hsite hij q hcard z hthree

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {k c e : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hck : c.1.1 = k.1.1)
  (hek : e.1.1 = k.1.1)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false))
  (hetag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e = (false, false))
  (hce : c ≠ e) :
-- imply
  3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair G sites hsite hij q hcard z hthree k c e hkK hk hcC heC hck hek hctag hetag hce

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {k c e : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3)
  (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hk : k.1.1 = lpReplicaCurrentSeamEdge sites j)
  (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
  (hck : c.1.1 = k.1.1)
  (hek : e.1.1 = k.1.1)
  (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c = (false, false))
  (hetag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e = (false, false))
  (hce : c ≠ e) :
-- imply
  3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair G sites hsite hij q hcard z hthree k c e hkK hk hcC heC hck hek hctag hetag hce

/--
[lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (_hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (houtput : Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) ≤ (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard G sites q _hcard houtput

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_five](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_five_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≤ 5)
  (hfiveOutput : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 → Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) ≤ (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_five G sites hsite hij q hle hfiveOutput


-- created on 2026-10-23
