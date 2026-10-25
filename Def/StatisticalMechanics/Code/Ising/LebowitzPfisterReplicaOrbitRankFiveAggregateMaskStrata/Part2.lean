/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u ∪
    lpReplicaOffdiagResolvableHighRowCrossTraceFiberRankFive
      G sites i j q u


noncomputable def lpReplicaLowRowCrossTraceOutputRowMaskTwo
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    ↑(lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u) →
      ↑(lpReplicaOffdiagBalancedOutputCrossTraceFiberRowMaskRankFive
        G sites i j q u 2) := by
  classical
  intro z
  let hz := Finset.mem_filter.mp z.2
  let d := lpReplicaLowRowMarkedOutputData
    G sites hsite hij q hcard z.1 hz.2
  refine ⟨d.output, ?_⟩
  have hmem := lpReplicaLowRowMarkedOutputData_mem_targetFiberRowMaskTwo
    G sites hsite hij q hcard z.1 hz.2 d
  have htrace := (Finset.mem_filter.mp hz.1).2
  simpa only [htrace] using hmem


end
end StatMech.Ising
