/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaBalancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (B D : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  profile : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  orbit : lpReplicaSymmetrizedProfile G sites profile = q
  tag : Copy (lpReplicaCurrentGraph G sites) profile -> LPReplicaRowTag
  gate : LPReplicaRowGate G sites profile B ∅ tag
  orbitLabel : LPReplicaProfileOrbitLabel G sites q profile
  selector : Finset (Copy (lpReplicaCurrentGraph G sites) profile)
  falseSource : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (selector.filter fun c => (tag c).2 = false) = D
  trueSource : StatMech.Sharpness.RandomCurrent.sources
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (selector.filter fun c => (tag c).2 = true) = ∅
  row0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (lpReplicaRowCopies G sites profile
      (lpReplicaToggleRows G sites profile selector tag) false)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  row1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK
    (endsM (lpReplicaCurrentGraph G sites) profile)
    (lpReplicaRowCopies G sites profile
      (lpReplicaToggleRows G sites profile selector tag) true)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1


end
end StatMech.Ising
