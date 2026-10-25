/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaProfileOrbitLabelReallocates
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (M : LPReplicaProfileOrbitLabel G sites q n) : Prop :=
  forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    ∃ R T : Finset (Fin (q e.1)),
      R ⊆ (L e).1 ∧
      T ⊆ Finset.univ \ (L e).1 ∧
      (M e).1 = ((L e).1 \ R) ∪ T


end
end StatMech.Ising
