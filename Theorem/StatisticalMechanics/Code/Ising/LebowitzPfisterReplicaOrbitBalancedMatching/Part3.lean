/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagBalancedMatch_iff_output
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagBalancedMatch G sites i j q z y ↔
      LPReplicaOffdiagBalancedOutput G sites i j q y := by
  dsimp only [LPReplicaOffdiagBalancedMatch,
    LPReplicaOffdiagBalancedOutput]
  constructor
  · rintro (⟨s, _, hy⟩ | ⟨s, _, hy⟩)
    · exact Or.inl ⟨s, hy⟩
    · exact Or.inr ⟨s, hy⟩
  · rintro (⟨s, hy⟩ | ⟨s, hy⟩)
    · exact Or.inl ⟨s,
        lpReplicaProfileOrbitLabelReallocates_all
          G sites q z.2.2 s.orbitLabel, hy⟩
    · exact Or.inr ⟨s,
        lpReplicaProfileOrbitLabelReallocates_all
          G sites q z.2.2 s.orbitLabel, hy⟩


end
end StatMech.Ising
