import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q z)
  (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
-- imply
  (lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2).card = 4 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_rank_five_highRow_singletonToggle_mask_four G sites hsite hij q hcard z hhigh y c hstate

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow_eq
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
  (hresolve : LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive G sites i j q z) :
-- imply
  (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 4).Nonempty := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskFour_rank_five_nonempty_of_resolvableHighRow G sites hsite hij q hcard z hresolve

/--
[lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  d.output ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) 2 := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo G sites hsite hij q hcard z hlow d

/--
[lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  ¬ (y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q u 2 ∧ y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q u 4) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskTwo_disjoint_four G sites i j q u y

/--
[lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget_eq
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
  (lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive G sites i j q u 4).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive_card_le_maskFourTarget G sites hsite hij q hcard u

/--
[lpReplicaLowRowCrossTraceOutputRowMaskTwo_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaLowRowCrossTraceOutputRowMaskTwo_val_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {z : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaLowRowCrossTraceOutputRowMaskTwo G sites hsite hij q hcard u z).1 = (lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u z).1 := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowCrossTraceOutputRowMaskTwo_val G sites hsite hij q hcard u z

/--
[lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective_eq
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
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hinjective : Function.Injective (lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u)) :
-- imply
  (lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive G sites i j q u).card <= (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective G sites hsite hij q hcard u hinjective


-- created on 2026-10-23
