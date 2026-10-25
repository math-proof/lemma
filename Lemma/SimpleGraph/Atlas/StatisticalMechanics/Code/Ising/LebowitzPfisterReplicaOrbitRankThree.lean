import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankThree
open Finset StatMech StatMech.Ising


/--
[randomCurrent_sources_singleton_of_ends_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma randomCurrent_sources_singleton_of_ends_eq_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {c : ι}
  {x y : W}
-- given
  (hxy : x ≠ y)
  (hc : ends c = s(x, y)) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends {c} = {x, y} := by
-- proof
  apply StatMech.Ising.randomCurrent_sources_singleton_of_ends_eq ends c hxy hc

/--
[lpReplicaProfileCopyEquivCommonSlot_eq_inl_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivCommonSlot_eq_inl_of_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
-- imply
  ∃ x, lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c = Sum.inl x := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivCommonSlot_eq_inl_of_fixed G sites q m hm L c hfixed

/--
[lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites) :
-- imply
  lpReplicaOrbitFourColorSlotReflect G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c}) s = s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed G sites q m hm L c hfixed s

/--
[lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i : I}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hc : c.1.1 = s(lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i)) :
-- imply
  c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc

/--
[card_lpReplicaMatchingSeamSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma card_lpReplicaMatchingSeamSource_eq
  [Fintype V]
  [DecidableEq V]
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i).card = 2 := by
-- proof
  apply StatMech.Ising.card_lpReplicaMatchingSeamSource sites i

/--
[card_lpReplicaMatchingSeamSymmDiffGhost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma card_lpReplicaMatchingSeamSymmDiffGhost_eq
  [Fintype V]
  [DecidableEq V]
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1).card = 4 := by
-- proof
  apply StatMech.Ising.card_lpReplicaMatchingSeamSymmDiffGhost sites i

/--
[lpReplicaOrientedFourColorSlotState_cast_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorSlotState_cast_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A D E : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaDecoratedOrbitAtom G sites A D q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : D = E) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites A E q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A E q (cast (congrArg (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x)) = lpReplicaOrientedFourColorSlotState G sites A D q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A D q x) := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorSlotState_cast_boundary G sites A D E q h x

/--
[lpReplicaOffdiagDecoratedTargetBranchedSlotState_right_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTargetBranchedSlotState_right_eq_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaDecoratedOrbitAtom G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inr y)).2 = (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q (Sum.inl y)).2 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTargetBranchedSlotState_right_eq_left G sites i j q y

/--
[lpReplicaCurrentGraph_adj_ghost0_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaCurrentGraph_adj_ghost0_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentGraph G sites).Adj (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) x ↔ ∃ v : V, x = .inl (.inl v) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGraph_adj_ghost0_iff G sites x

/--
[lpReplicaCurrentGraph_adj_ghost1_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaCurrentGraph_adj_ghost1_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentGraph G sites).Adj (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) x ↔ ∃ v : V, x = .inl (.inr v) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGraph_adj_ghost1_iff G sites x

/--
[lpReplicaCurrentEdge_eq_ghost0_left_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_eq_ghost0_left_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : Sym2 (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (he : e ∈ (lpReplicaCurrentGraph G sites).edgeFinset)
  (hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ e) :
-- imply
  ∃ v : V, e = s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V), (.inl (.inl v) : LPReplicaCurrentVertex V)) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_eq_ghost0_left_of_mem G sites e he hghost

/--
[lpReplicaCurrentEdge_eq_ghost1_right_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_eq_ghost1_right_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : Sym2 (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (he : e ∈ (lpReplicaCurrentGraph G sites).edgeFinset)
  (hghost : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ e) :
-- imply
  ∃ v : V, e = s((lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V), (.inl (.inr v) : LPReplicaCurrentVertex V)) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_eq_ghost1_right_of_mem G sites e he hghost

/--
[sym2_eq_mk_of_mem_of_mem_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma sym2_eq_mk_of_mem_of_mem_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {e : Sym2 W}
  {x y : W}
-- given
  (hx : x ∈ e)
  (hy : y ∈ e)
  (hxy : x ≠ y) :
-- imply
  e = s(x, y) := by
-- proof
  apply StatMech.Ising.sym2_eq_mk_of_mem_of_mem_of_ne hx hy hxy

/--
[lpReplicaOffdiagDecoratedSource_rank_three_endpointSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_endpointSupport_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) z.1.1.1 (Finset.univ.biUnion fun c => (E c).toFinset) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_endpointSupport G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_three_endpoints_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_endpoints_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c d : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
  (hcd : c ≠ d) :
-- imply
  Disjoint (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) z.1.1.1 c).toFinset (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) z.1.1.1 d).toFinset := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_endpoints_disjoint G sites hsite hij q hcard z c d hcd

/--
[lpReplicaOffdiagDecoratedSource_rank_three_exists_seamCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_exists_seamCopy_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  (∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨ ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_exists_seamCopy G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_three_rowMask_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_rowMask_eq_univ_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_rowMask_eq_univ G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_three_swapped_all_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_swapped_all_false_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z ∀ c, d.1 c = (false, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_swapped_all_false G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_three_orientedTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_orientedTag_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  let B := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z ∀ c, lpReplicaOrientedFourColorTag G sites ∅ B q oz c = (true, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_orientedTag G sites hsite hij q hcard z

/--
[lpReplicaOrientedFourColorAtom_rank_three_all_falseCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorAtom_rank_three_all_falseCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {z : LPReplicaOrientedFourColorAtom G sites A B q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
  (hA : A.card = 2)
  (hB : (B.map lpReplicaCurrentReflect.toEmbedding).card = 4) :
-- imply
  ∀ c, (lpReplicaOrientedFourColorTag G sites A B q z c).2 = false := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorAtom_rank_three_all_falseCurrent G sites A B q hcard hA hB z

/--
[lpReplicaBalancedSelector_rank_three_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaBalancedSelector_rank_three_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
  (sourceTag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
  (hbase : ∀ a, s.tag a = (false, false))
  (hsource : ∀ a, sourceTag a = (true, false))
  (hselector : s.selector = Finset.univ \ {c})
  (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites)
  (hSiCard : Si.card = 2)
  (hDCard : (Sj ∆ T).card = 4) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomOfBalancedSelector G sites Si Sj T q s)) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit s.orbitLabel {c}) (lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit s.orbitLabel sourceTag) := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedSelector_rank_three_slotState G sites Si Sj T q hcard s c sourceTag hbase hsource hselector hfixed hSiCard hDCard

/--
[lpReplicaOffdiagDecoratedSource_rank_three_exists_balancedSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_exists_balancedSelector_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (∃ s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q, ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ c.1.1 = s(lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i) ∧ HEq s.selector (Finset.univ \ {c}) ∧ (∀ a, s.tag a = (false, false)) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inl (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites i j q s))).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) ∨ (∃ s : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q, ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ c.1.1 = s(lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j) ∧ HEq s.selector (Finset.univ \ {c}) ∧ (∀ a, s.tag a = (false, false)) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inr (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites j i q s))).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_exists_balancedSelector G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_three_eq_of_crossTrace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_eq_of_crossTrace_eq_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
  (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) :
-- imply
  z = w := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_eq_of_crossTrace_eq G sites hsite hij q hcard z w htrace

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_three_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_three_card_le_one_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤ 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_three_card_le_one G sites hsite hij q hcard u

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_three_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_three_nonempty_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_three_nonempty G sites hsite hij q hcard z

/--
[lpReplicaOffdiagCrossTraceFiberCards_rank_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossTraceFiberCards_rank_three_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossTraceFiberCards_rank_three G sites hsite hij q hcard u

/--
[lpReplicaOffdiagCrossToggleMaskHall_rank_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_rank_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_rank_three G sites hsite hij q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_rank_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankThree.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_rank_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_rank_three G sites hsite hij q hcard


-- created on 2026-10-23
