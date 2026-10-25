import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
open Finset StatMech StatMech.Ising


/--
[lpReplicaRowTagEquivFin4_symm_rowToggleFin4_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaRowTagEquivFin4_symm_rowToggleFin4_snd_eq
  [Fintype V]
  [DecidableEq V]
  {a : Fin 4} :
-- imply
  (lpReplicaRowTagEquivFin4.symm (lpReplicaRowToggleFin4 a)).2 = (lpReplicaRowTagEquivFin4.symm a).2 := by
-- proof
  apply StatMech.Ising.lpReplicaRowTagEquivFin4_symm_rowToggleFin4_snd a

/--
[lpReplicaOrbitFourColorSlotCrossToggle_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_current_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaRowTagEquivFin4.symm ((lpReplicaOrbitFourColorSlotCrossToggle G sites q P s).color ⟨x, Finset.mem_univ _⟩)).2 = (lpReplicaRowTagEquivFin4.symm (s.color ⟨x, Finset.mem_univ _⟩)).2 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_current G sites q P s x

/--
[nonempty_lpReplicaLowRowMarkedOutputData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma nonempty_lpReplicaLowRowMarkedOutputData_eq
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
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  Nonempty (LPReplicaLowRowMarkedOutputData G sites q z) := by
-- proof
  apply StatMech.Ising.nonempty_lpReplicaLowRowMarkedOutputData G sites hsite hij q hcard z hlow

/--
[lpReplicaLowRowMarkedOutputData_mem_targetFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaLowRowMarkedOutputData_mem_targetFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  d.output ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowMarkedOutputData_mem_targetFiber G sites q z d

/--
[lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two_eq
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
  (lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q d.output).2).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowMarkedOutputData_rowMask_card_eq_two G sites hsite hij q hcard z hlow d

/--
[lpReplicaOffdiagDecoratedSourceSlotState_current_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceSlotState_current_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaRowTagEquivFin4.symm ((lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z).color ⟨lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1 z.1.1.2 z.2.2 c, Finset.mem_univ _⟩)).2 = ((lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c).2 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceSlotState_current_copy G sites i j q z c

/--
[lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {z w : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hzw : z ≠ w)
  (hout : lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u z = lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u w) :
-- imply
  Nonempty (LPReplicaLowRowCollisionParallelData G sites i j q z.1) := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowCrossTraceOutput_collision_parallelData_nonempty G sites hsite hij q hcard u z w hzw hout

/--
[lpReplicaLowRowCrossTraceOutput_collision_card_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaLowRowCrossTraceOutput_collision_card_ge_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {u : LPReplicaOrbitFourColorSlotState G sites q}
  {z w : ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hzw : z ≠ w)
  (hout : lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u z = lpReplicaLowRowCrossTraceOutput G sites hsite hij q hcard u w) :
-- imply
  3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowCrossTraceOutput_collision_card_ge_three G sites hsite hij q hcard u z w hzw hout

/--
[lpReplicaOffdiagLowRowCrossTraceFiberRankFive_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowRowCrossTraceFiberRankFive_card_le_target_eq
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
  (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u).card ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowRowCrossTraceFiberRankFive_card_le_target G sites hsite hij q hcard u

/--
[lpReplicaOffdiagLowRowSourcesRankFive_card_eq_sum_traceFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowRowSourcesRankFive_card_eq_sum_traceFibers_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagLowRowSourcesRankFive G sites i j q).card = ∑ u : LPReplicaOrbitFourColorSlotState G sites q, (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive G sites i j q u).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowRowSourcesRankFive_card_eq_sum_traceFibers G sites i j q

/--
[lpReplicaOffdiagLowRowSourcesRankFive_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma lpReplicaOffdiagLowRowSourcesRankFive_card_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (lpReplicaOffdiagLowRowSourcesRankFive G sites i j q).card ≤ Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagLowRowSourcesRankFive_card_le_target G sites hsite hij q hcard

/--
[card_lpReplicaAggregateLowRowSourceRankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma card_lpReplicaAggregateLowRowSourceRankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaAggregateLowRowSourceRankFive G sites q) = ∑ i : I, ∑ j : I, if i = j then 0 else (lpReplicaOffdiagLowRowSourcesRankFive G sites i j q).card := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateLowRowSourceRankFive G sites q

/--
[card_lpReplicaAggregateLowRowSourceRankFive_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean)
-/
@[path]
private lemma card_lpReplicaAggregateLowRowSourceRankFive_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card (LPReplicaAggregateLowRowSourceRankFive G sites q) ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.card_lpReplicaAggregateLowRowSourceRankFive_le_target G sites hsite q hcard


-- created on 2026-10-23
