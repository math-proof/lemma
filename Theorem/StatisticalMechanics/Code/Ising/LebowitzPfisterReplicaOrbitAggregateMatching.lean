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
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateDecoratedSource_indices_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaAggregateDecoratedSource G sites q) :
    z.1 ≠ z.2.1 := by
  rcases z with ⟨i, j, w, atom⟩
  dsimp only
  intro hij
  subst j
  have w0 : Fin 0 := by simpa using w
  exact Fin.elim0 w0


end
end StatMech.Ising
