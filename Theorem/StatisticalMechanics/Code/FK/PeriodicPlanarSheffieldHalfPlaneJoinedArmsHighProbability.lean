/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem exists_nat_abs_bound_on_finset (S : Finset V) (f : V → Real) :
    ∃ K : Nat, ∀ x ∈ S, |f x| ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨K, hK⟩ := exists_nat_ge (max |f a| N)
      refine ⟨K, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact (le_max_left _ _).trans hK
      · exact (hN x hxS).trans ((le_max_right _ _).trans hK)


end StatMech.FK.PeriodicPlanar
