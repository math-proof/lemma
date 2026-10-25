/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfileOrbitLabelReallocates_all
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (M : LPReplicaProfileOrbitLabel G sites q n) :
    LPReplicaProfileOrbitLabelReallocates G sites q L M := by
  intro e
  let R := (L e).1 \ (M e).1
  let T := (M e).1 \ (L e).1
  refine ⟨R, T, Finset.sdiff_subset, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  · ext x
    simp only [R, T, Finset.mem_union, Finset.mem_sdiff]
    tauto

end
end StatMech.Ising
