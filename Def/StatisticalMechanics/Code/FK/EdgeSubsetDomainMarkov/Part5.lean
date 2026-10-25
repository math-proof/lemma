/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def edgeSubsetExteriorComponentEquiv
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V))
    (A : SimpleGraph V) :
    (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).ConnectedComponent ≃
      (A ⊔ edgeSubsetInducedWiring K H B psi).ConnectedComponent := by
  let L := A ⊔ edgeSubsetFrozenExteriorGraph K H B psi
  let R := A ⊔ edgeSubsetInducedWiring K H B psi
  apply Equiv.ofBijective (fun C : L.ConnectedComponent =>
    R.connectedComponentMk C.out)
  constructor
  · intro C D hCD
    have hR : R.Reachable C.out D.out := ConnectedComponent.eq.mp hCD
    have hL : L.Reachable C.out D.out :=
      (sup_edgeSubsetFrozen_reachable_iff_induced
        K H B psi A C.out D.out).mpr hR
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hL
  · intro D
    let C := L.connectedComponentMk D.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hL : L.Reachable C.out D.out := ConnectedComponent.exact C.out_eq
    exact (sup_edgeSubsetFrozen_reachable_iff_induced
      K H B psi A C.out D.out).mp hL

end
end StatMech.FK
