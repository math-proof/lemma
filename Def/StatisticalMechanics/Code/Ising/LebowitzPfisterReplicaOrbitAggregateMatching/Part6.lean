/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAggregateMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part3
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaAggregateSelectedTargetFiberEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) (k : I) :
    {y : LPReplicaAggregateDecoratedTarget G sites q // y.2.1 = k} ≃
      Fin 2 × Sigma fun j : I =>
        LPReplicaDecoratedOrbitAtom G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q := by
  classical
  refine {
    toFun := ?_
    invFun := ?_
    left_inv := ?_
    right_inv := ?_
  }
  · rintro ⟨⟨b, ⟨i, ⟨j, atom⟩⟩⟩, hi⟩
    dsimp only at hi
    subst i
    exact ⟨b, ⟨j, atom⟩⟩
  · rintro ⟨b, ⟨j, atom⟩⟩
    exact ⟨⟨b, ⟨k, ⟨j, atom⟩⟩⟩, rfl⟩
  · rintro ⟨⟨b, ⟨i, ⟨j, atom⟩⟩⟩, hi⟩
    dsimp only at hi
    subst i
    rfl
  · rintro ⟨b, ⟨j, atom⟩⟩
    rfl


end
end StatMech.Ising
