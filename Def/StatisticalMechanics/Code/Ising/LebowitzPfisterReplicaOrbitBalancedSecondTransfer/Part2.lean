/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaBalancedSelectorOfComponentExchange
    (G : SimpleGraph V) (sites : I -> V)
    (B : Finset (LPReplicaCurrentVertex V))
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (orbitLabel : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaBalancedSelector G sites B
      (B ∩ StatMech.Sharpness.RandomCurrent.compOf
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag false)
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)) q := by
  let selector := lpReplicaBalancedComponentSelector G sites m tag
  have hsources := lpReplicaBalancedComponentSelector_sources
    G sites m B tag hgate
  have hdisconn := lpReplicaBalancedComponentSelector_disconnects
    G sites m B tag hgate
  exact
    { profile := m
      orbit := horbit
      tag := tag
      gate := hgate
      orbitLabel := orbitLabel
      selector := selector
      falseSource := hsources.1
      trueSource := hsources.2
      row0Disconn := hdisconn.1
      row1Disconn := hdisconn.2 }


noncomputable def lpReplicaDecoratedOrbitAtomOfBalancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    LPReplicaDecoratedOrbitAtom G sites Si
      ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q := by
  let movedTag := lpReplicaToggleRows G sites s.profile s.selector s.tag
  have hgate : LPReplicaRowGate G sites s.profile Si (Sj ∆ T) movedTag :=
    lpReplicaRowGate_toggle_offdiag G sites s.profile Si Sj T
      s.tag s.selector s.gate s.falseSource s.trueSource
      s.row0Disconn s.row1Disconn
  exact lpReplicaDecoratedOrbitAtomOfRowGate G sites s.profile q movedTag
    Si (Sj ∆ T) s.orbit hgate s.orbitLabel


end
end StatMech.Ising
