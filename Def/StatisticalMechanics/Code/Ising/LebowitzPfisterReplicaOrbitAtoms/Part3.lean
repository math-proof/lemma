/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaOffdiagOrbitAtomCardInequality
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  Fintype.card (LPReplicaOrbitAtom G sites ∅ (Si ∆ Sj ∆ T) q) <=
    Fintype.card (LPReplicaOrbitAtom G sites Si (Sj ∆ T) q) +
      Fintype.card (LPReplicaOrbitAtom G sites Sj (Si ∆ T) q)


end
end StatMech.Ising
