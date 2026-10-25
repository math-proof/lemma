/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitTagReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitTagReconstruction
open Finset


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaRowCopies_true_eq_compl_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaRowCopies G sites m tag true =
      Finset.univ \ lpReplicaRowCopies G sites m tag false := by
  ext c
  simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  cases (tag c).1 <;> simp


end
end StatMech.Ising
