/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredEndpoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEuler
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierD

noncomputable section

theorem boundaryCliqueGraph_reachable_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V -> Prop) [DecidablePred bdry] (x y : V) :
    (boundaryCliqueGraph bdry).Reachable x y <->
      x = y ∨ (bdry x ∧ bdry y) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact Or.inl rfl
    | @cons u v w huv p ih =>
        have huv' := (boundaryCliqueGraph_adj bdry u v).1 huv
        rcases ih with rfl | ⟨hv, hw⟩
        · exact Or.inr ⟨huv'.2.1, huv'.2.2⟩
        · exact Or.inr ⟨huv'.2.1, hw⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact SimpleGraph.Reachable.refl _
    · by_cases hxy : x = y
      · subst y
        exact SimpleGraph.Reachable.refl _
      · exact ((boundaryCliqueGraph_adj bdry x y).2
          ⟨hxy, hx, hy⟩).reachable

end
end StatMech.Universality
