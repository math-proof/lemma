/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

def LPReplicaRowGate (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) : Prop :=
  let H := lpReplicaCurrentGraph G sites
  let e := endsM H m
  RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag false false) = A ∧
    RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag false true) = ∅ ∧
    ¬ RandomCurrent.connK e (lpReplicaRowCopies G sites m tag false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 ∧
    RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag true false) = B ∧
    RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag true true) = ∅ ∧
    ¬ RandomCurrent.connK e (lpReplicaRowCopies G sites m tag true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1

end
end StatMech.Ising
