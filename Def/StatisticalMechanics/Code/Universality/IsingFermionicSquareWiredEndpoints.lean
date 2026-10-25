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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredEndpoints
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierD

noncomputable section

noncomputable def boundaryCliqueComponentEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (bdry : V -> Prop) [DecidablePred bdry]
    (v0 : V) (hv0 : bdry v0) :
    Option {x : V // ¬ bdry x} ≃
      (boundaryCliqueGraph bdry).ConnectedComponent := by
  let f : Option {x : V // ¬ bdry x} ->
      (boundaryCliqueGraph bdry).ConnectedComponent
    | none => (boundaryCliqueGraph bdry).connectedComponentMk v0
    | some x => (boundaryCliqueGraph bdry).connectedComponentMk x.1
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some y =>
            exfalso
            have hreach := ConnectedComponent.eq.mp hab
            have hclass := (boundaryCliqueGraph_reachable_iff
              bdry v0 y.1).1 hreach
            rcases hclass with h | h
            · exact y.2 (h ▸ hv0)
            · exact y.2 h.2
    | some x =>
        cases b with
        | none =>
            exfalso
            have hreach := ConnectedComponent.eq.mp hab
            have hclass := (boundaryCliqueGraph_reachable_iff
              bdry x.1 v0).1 hreach
            rcases hclass with h | h
            · exact x.2 (h.symm ▸ hv0)
            · exact x.2 h.1
        | some y =>
            have hreach := ConnectedComponent.eq.mp hab
            have hclass := (boundaryCliqueGraph_reachable_iff
              bdry x.1 y.1).1 hreach
            have hxy : x.1 = y.1 := by
              rcases hclass with h | h
              · exact h
              · exact False.elim (x.2 h.1)
            exact congrArg some (Subtype.ext hxy)
  · intro C
    by_cases hC : bdry C.out
    · refine ⟨none, ?_⟩
      rw [← C.out_eq]
      apply ConnectedComponent.sound
      exact (boundaryCliqueGraph_reachable_iff bdry v0 C.out).2
        (Or.inr ⟨hv0, hC⟩)
    · refine ⟨some ⟨C.out, hC⟩, ?_⟩
      exact C.out_eq

end
end StatMech.Universality
