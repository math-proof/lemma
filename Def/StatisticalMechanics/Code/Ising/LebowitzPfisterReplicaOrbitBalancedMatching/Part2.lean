/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaOffdiagBalancedOutput
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  (∃ s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites i j q s)) ∨
    (∃ s : LPReplicaBalancedSelector G sites
      (Sj ∆ Si ∆ T) (Si ∆ T) q,
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites j i q s))


def LPReplicaOffdiagBalancedMatch
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : Prop :=
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  (∃ s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      LPReplicaProfileOrbitLabelReallocates G sites q z.2.2 s.orbitLabel ∧
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites i j q s)) ∨
    (∃ s : LPReplicaBalancedSelector G sites
      (Sj ∆ Si ∆ T) (Si ∆ T) q,
      LPReplicaProfileOrbitLabelReallocates G sites q z.2.2 s.orbitLabel ∧
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites j i q s))

end
end StatMech.Ising
