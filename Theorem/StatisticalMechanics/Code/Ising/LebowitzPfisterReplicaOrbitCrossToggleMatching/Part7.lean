/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberInjections
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hfiber : LPReplicaOffdiagCrossTraceFiberInjection G sites i j q) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  have hmove : Function.Injective hfiber.move := by
    intro z w hzw
    have htrace :
        lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
          lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w := by
      calc
        _ = lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q
            (hfiber.move z) := (hfiber.trace_eq z).symm
        _ = lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q
            (hfiber.move w) := congrArg
          (lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q) hzw
        _ = _ := hfiber.trace_eq w
    exact hfiber.injective_on_trace z w htrace hzw
  unfold LPReplicaOffdiagCrossToggleMaskHall
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective
    (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q)).mpr
  refine ⟨hfiber.move, hmove, ?_⟩
  intro z
  simp only [lpReplicaOffdiagCrossToggleMaskNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and,
    lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace]
  exact ⟨hfiber.output_mem z, hfiber.trace_eq z⟩


end
end StatMech.Ising
