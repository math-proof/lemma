import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagDecoratedSourceSlotState_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceSlotState_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q

/--
[lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective G sites i j q

/--
[lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagCrossToggleMaskRelated G sites i j q z y ↔ y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q ∧ lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y = lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace G sites i j q z y

/--
[lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Set.InjOn (fun z : LPReplicaOffdiagDecoratedSource G sites i j q => lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber G sites i j q u

/--
[lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Set.InjOn (fun y : LPReplicaOffdiagDecoratedTarget G sites i j q => ((lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).1, lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2)) (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber G sites i j q u

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_eq_masks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_eq_masks_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card = (lpReplicaOffdiagDecoratedSourceCrossTraceMasks G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_eq_masks G sites i j q u

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiber_card_eq_branchedMasks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiber_card_eq_branchedMasks_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card = (lpReplicaOffdiagBalancedOutputCrossTraceBranchedMasks G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiber_card_eq_branchedMasks G sites i j q u

/--
[lpReplica_half_ne_doubledBoundary_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplica_half_ne_doubledBoundary_of_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {X D : Finset (LPReplicaCurrentVertex V)}
-- given
  (hD : D = X ∆ X.map lpReplicaCurrentReflect.toEmbedding)
  (hDne : D.Nonempty) :
-- imply
  X ≠ D := by
-- proof
  apply StatMech.Ising.lpReplica_half_ne_doubledBoundary_of_nonempty X D hD hDne

/--
[lpReplicaDecoratedSourceCanonicalHalfBranch_not_directTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedSourceCanonicalHalfBranch_not_directTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 match lpReplicaDecoratedSourceCanonicalHalfBranch G sites hsite hij q z with := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedSourceCanonicalHalfBranch_not_directTarget G sites hsite hij q z

/--
[lpReplicaDecoratedSourceCanonicalHalfCandidate_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedSourceCanonicalHalfCandidate_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaDecoratedSourceCanonicalHalfCandidate G sites hsite hij q z).2.allocation = fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies G sites q z.1.1.1 z.1.1.2 (lpReplicaDecoratedSourceCanonicalHalfSelector G sites i j q z).selector z.2.2) e).1 := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedSourceCanonicalHalfCandidate_allocation G sites hsite hij q z

/--
[lpReplicaDecoratedSourceCanonicalHalfCandidate_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedSourceCanonicalHalfCandidate_color_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaDecoratedSourceCanonicalHalfCandidate G sites hsite hij q z).2.color = (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1 z.1.1.2 z.2.2 (lpReplicaToggleRows G sites z.1.1.1 (lpReplicaDecoratedSourceCanonicalHalfSelector G sites i j q z).selector (lpReplicaOrientedFourColorTag G sites ∅ (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) q z)))).color := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedSourceCanonicalHalfCandidate_color G sites hsite hij q z

/--
[lpReplicaDecoratedSourceCanonicalHalfCandidate_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaDecoratedSourceCanonicalHalfCandidate_eq_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z w : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaDecoratedSourceCanonicalHalfCandidate G sites hsite hij q z = lpReplicaDecoratedSourceCanonicalHalfCandidate G sites hsite hij q w ↔ lpReplicaDecoratedSourceCanonicalHalfBranchBit G sites hsite hij q z = lpReplicaDecoratedSourceCanonicalHalfBranchBit G sites hsite hij q w ∧ lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w ∧ lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∆ lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z = lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w) ∆ lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedSourceCanonicalHalfCandidate_eq_iff G sites hsite hij q z w

/--
[isEmpty_lpReplicaOrbitCommonSlot_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma isEmpty_lpReplicaOrbitCommonSlot_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  IsEmpty (LPReplicaOrbitCommonSlot G sites (fun _ => 0)) := by
-- proof
  apply StatMech.Ising.isEmpty_lpReplicaOrbitCommonSlot_zero G sites

/--
[isEmpty_lpReplicaOffdiagDecoratedSource_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma isEmpty_lpReplicaOffdiagDecoratedSource_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V) :
-- imply
  IsEmpty (LPReplicaOffdiagDecoratedSource G sites i j (fun _ => 0)) := by
-- proof
  apply StatMech.Ising.isEmpty_lpReplicaOffdiagDecoratedSource_zero G sites i j

/--
[lpReplicaOffdiagCrossToggleMaskHall_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j (fun _ => 0) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_zero G sites i j

/--
[randomCurrent_sources_subset_endpointSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma randomCurrent_sources_subset_endpointSupport_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {K : Finset E}
-- given
  (ends : E -> Sym2 W) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends K ⊆ K.biUnion fun e => (ends e).toFinset := by
-- proof
  apply StatMech.Ising.randomCurrent_sources_subset_endpointSupport ends K

/--
[card_randomCurrent_sources_le_two_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma card_randomCurrent_sources_le_two_mul_card_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {K : Finset E}
-- given
  (ends : E -> Sym2 W) :
-- imply
  (StatMech.Sharpness.RandomCurrent.sources ends K).card <= 2 * K.card := by
-- proof
  apply StatMech.Ising.card_randomCurrent_sources_le_two_mul_card ends K

/--
[card_lpReplica_offdiagSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma card_lpReplica_offdiagSource_eq
  [Fintype V]
  [DecidableEq V]
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j) :
-- imply
  (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1).card = 6 := by
-- proof
  apply StatMech.Ising.card_lpReplica_offdiagSource sites hsite hij

/--
[isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
-- imply
  IsEmpty (LPReplicaOffdiagDecoratedSource G sites i j q) := by
-- proof
  apply StatMech.Ising.isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two G sites hsite hij q hcard

/--
[lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two G sites hsite hij q hcard

/--
[lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies_eq
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
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = Finset.univ ∧ ∀ c, d.1 c = (true, false) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies G sites hsite hij q hcard z

/--
[lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
  {z w : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) :
-- imply
  z = w := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots G sites i j q z w htrace

/--
[lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card <= 1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots G sites i j q u

/--
[lpReplicaOffdiagCrossTraceFiber_card_of_isEmptySlots_of_target_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossTraceFiber_card_of_isEmptySlots_of_target_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (htarget : (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).Nonempty) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossTraceFiber_card_of_isEmptySlots_of_target_nonempty G sites i j q u htarget

/--
[lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q z = lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber G sites i j q z

/--
[lpReplicaOffdiagDecoratedSource_card_eq_sum_crossTraceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_card_eq_sum_crossTraceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {U : Finset (LPReplicaOrbitFourColorSlotState G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hU : forall z : LPReplicaOffdiagDecoratedSource G sites i j q, lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z ∈ U) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) = ∑ u ∈ U, (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_card_eq_sum_crossTraceFibers G sites i j q U hU

/--
[lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {U : Finset (LPReplicaOrbitFourColorSlotState G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hU : forall y, y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q -> lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y ∈ U) :
-- imply
  (lpReplicaOffdiagBalancedOutputs G sites i j q).card = ∑ u ∈ U, (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers G sites i j q U hU

/--
[lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : forall u : LPReplicaOrbitFourColorSlotState G sites q, (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards G sites i j q hcard

/--
[lpReplicaOffdiagCrossTraceFiberCards_of_maskHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossTraceFiberCards_of_maskHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hHall : LPReplicaOffdiagCrossToggleMaskHall G sites i j q) :
-- imply
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossTraceFiberCards_of_maskHall G sites i j q hHall u

/--
[lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q ↔ forall u : LPReplicaOrbitFourColorSlotState G sites q, (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards G sites i j q

/--
[lpReplicaOffdiagCrossToggleMaskHall_iff_traceFiberEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_iff_traceFiberEmbeddings_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q ↔ forall u : LPReplicaOrbitFourColorSlotState G sites q, Nonempty (LPReplicaOffdiagCrossTraceFiberEmbedding G sites i j q u) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_iff_traceFiberEmbeddings G sites i j q

/--
[lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberInjections_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hfiber : LPReplicaOffdiagCrossTraceFiberInjection G sites i j q) :
-- imply
  LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberInjections G sites i j q hfiber

/--
[LPReplicaOffdiagCrossToggleSelector.output_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma output_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCrossToggleSelector G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective s.output := by
-- proof
  apply StatMech.Ising.LPReplicaOffdiagCrossToggleSelector.output_injective G sites i j q s

/--
[nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Nonempty (LPReplicaOffdiagCrossToggleSelector G sites i j q) ↔ Nonempty (LPReplicaOffdiagCrossToggleMatching G sites i j q) := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaOffdiagCrossToggleSelector_iff_matching G sites i j q

/--
[nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Nonempty (LPReplicaOffdiagCrossToggleMatching G sites i j q) ↔ LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaOffdiagCrossToggleMatching_iff_maskHall G sites i j q

/--
[nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Nonempty (LPReplicaOffdiagCrossToggleSelector G sites i j q) ↔ LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaOffdiagCrossToggleSelector_iff_maskHall G sites i j q

/--
[lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCrossToggleSelector G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagBalancedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCard_of_crossToggleSelector G sites i j q s

/--
[lpReplicaOffdiagBalancedHall_of_crossToggleSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedHall_of_crossToggleSelector_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCrossToggleSelector G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagBalancedHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedHall_of_crossToggleSelector G sites i j q s

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCrossToggleSelector G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleSelector G sites i j q s

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hHall : LPReplicaOffdiagCrossToggleMaskHall G sites i j q) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall G sites i j q hHall

/--
[lpReplicaOffdiagOrbitAtomCardInequality_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j (fun _ => 0) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_zero G sites i j

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two G sites hsite hij q hcard


-- created on 2026-10-23
