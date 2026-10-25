/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaDecoratedOrbitAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaDecoratedOrbitAtom G sites A B q) =
      Fintype.card (LPReplicaOrbitAtom G sites A B q) := by
  classical
  rw [card_lpReplicaOrbitAtom]
  unfold LPReplicaDecoratedOrbitAtom
  change Fintype.card
      (Σ x : LPReplicaOrbitConfiguration G sites A B q,
        LPReplicaCollisionSplitLabel G sites x.1.1 x.2.1.1 ×
          LPReplicaProfileOrbitLabel G sites q x.1.1) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.card_prod,
    card_lpReplicaCollisionSplitLabel,
    card_lpReplicaProfileOrbitLabel]
  rfl


end
end StatMech.Ising
