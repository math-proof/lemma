import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
open Finset StatMech StatMech.Ising


/--
[randomCurrent_sources_singleton_nonempty_of_edgeCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma randomCurrent_sources_singleton_nonempty_of_edgeCopy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) {c}).Nonempty := by
-- proof
  apply StatMech.Ising.randomCurrent_sources_singleton_nonempty_of_edgeCopy G sites m c

/--
[lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = Finset.univ ∧ ∀ c, d.1 c = (true, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_four_rowMask_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_four_rowMask_eq_univ_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_four_rowMask_eq_univ G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_four_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_four_card_le_one_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤ 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_four_card_le_one G sites hsite hij q hcard u

/--
[lpReplicaOffdiagDecoratedSource_rank_four_swapped_all_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_four_swapped_all_false_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z ∀ c, d.1 c = (false, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_four_swapped_all_false G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_rank_four_orientedTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_four_orientedTag_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  let B := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z ∀ c, lpReplicaOrientedFourColorTag G sites ∅ B q oz c = (true, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_four_orientedTag G sites hsite hij q hcard z

/--
[sum_randomCurrent_degK_le_two_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma sum_randomCurrent_degK_le_two_mul_card_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {K : Finset E}
  {S : Finset W}
-- given
  (ends : E -> Sym2 W) :
-- imply
  (∑ x ∈ S, StatMech.Sharpness.RandomCurrent.degK ends K x) ≤ 2 * K.card := by
-- proof
  apply StatMech.Ising.sum_randomCurrent_degK_le_two_mul_card ends K S

/--
[lpReplicaOffdiagDecoratedSource_rank_four_exists_seamCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_four_exists_seamCopy_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  (∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨ ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_four_exists_seamCopy G sites hsite hij q hcard z

/--
[lpReplicaOrientedFourColorAtom_rank_four_all_falseCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorAtom_rank_four_all_falseCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {z : LPReplicaOrientedFourColorAtom G sites A B q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
  (hA : A.card = 2)
  (hB : (B.map lpReplicaCurrentReflect.toEmbedding).card = 4) :
-- imply
  ∀ c, (lpReplicaOrientedFourColorTag G sites A B q z c).2 = false := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorAtom_rank_four_all_falseCurrent G sites A B q hcard hA hB z

/--
[lpReplicaBalancedSelector_rank_four_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaBalancedSelector_rank_four_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) s.profile}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
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
  apply StatMech.Ising.lpReplicaBalancedSelector_rank_four_slotState G sites Si Sj T q hcard s c sourceTag hbase hsource hselector hfixed hSiCard hDCard

/--
[lpReplicaOffdiagDecoratedSource_rank_four_exists_balancedSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_four_exists_balancedSelector_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (∃ s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T) (Sj ∆ T) q, ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ c.1.1 = s(lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i) ∧ HEq s.selector (Finset.univ \ {c}) ∧ (∀ a, s.tag a = (false, false)) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inl (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites i j q s))).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) ∨ (∃ s : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q, ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1, s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧ c.1.1 = s(lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j) ∧ HEq s.selector (Finset.univ \ {c}) ∧ (∀ a, s.tag a = (false, false)) ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q (Sum.inr (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left G sites j i q s))).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_four_exists_balancedSelector G sites hsite hij q hcard z

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_four_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_four_nonempty_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_four_nonempty G sites hsite hij q hcard z

/--
[lpReplicaOffdiagCrossTraceFiberCards_rank_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossTraceFiberCards_rank_four_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossTraceFiberCards_rank_four G sites hsite hij q hcard u

/--
[lpReplicaOffdiagCrossToggleMaskHall_rank_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_rank_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_rank_four G sites hsite hij q hcard

/--
[lpReplicaOffdiagOrbitAtomCardInequality_rank_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFour.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_rank_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_rank_four G sites hsite hij q hcard


-- created on 2026-10-23
