/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagBalancedNeighbors
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaOffdiagBalancedMatch G sites i j q z y


noncomputable def lpReplicaOffdiagBalancedOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter
    (LPReplicaOffdiagBalancedOutput G sites i j q)


noncomputable def lpReplicaOffdiagBalancedLeftOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  exact Finset.univ.filter fun y =>
    ∃ s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      y = Sum.inl
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites i j q s)


noncomputable def lpReplicaOffdiagBalancedRightOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  exact Finset.univ.filter fun y =>
    ∃ s : LPReplicaBalancedSelector G sites
      (Sj ∆ Si ∆ T) (Si ∆ T) q,
      y = Sum.inr
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
          G sites j i q s)


def lpReplicaOffdiagDecoratedTargetProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedTarget G sites i j q ->
      (lpReplicaCurrentGraph G sites).edgeFinset -> Nat
  | Sum.inl y => y.1.1.1
  | Sum.inr y => y.1.1.1


noncomputable def lpReplicaOffdiagDecoratedSourcesAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z => z.1.1.1 = m


noncomputable def lpReplicaOffdiagBalancedLeftOutputsAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetProfile G sites i j q y = m


noncomputable def lpReplicaOffdiagBalancedRightOutputsAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedRightOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetProfile G sites i j q y = m


noncomputable def lpReplicaOffdiagBalancedRelevantProfiles
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) := by
  classical
  exact ((Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)).image
      (fun z => z.1.1.1)) ∪
    (lpReplicaOffdiagBalancedLeftOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetProfile G sites i j q) ∪
    (lpReplicaOffdiagBalancedRightOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetProfile G sites i j q)

end
end StatMech.Ising
