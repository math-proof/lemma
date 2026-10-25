/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCoupledPairedMatch_iff_output
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagCoupledPairedMatch G sites i j q z y ↔
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y := by
  constructor
  · exact And.left
  · intro hy
    exact ⟨hy, lpReplicaProfileOrbitLabelReallocates_all G sites q
      z.2.2 (lpReplicaOffdiagDecoratedTargetOrbitLabel G sites i j q y)⟩

end
end StatMech.Ising
