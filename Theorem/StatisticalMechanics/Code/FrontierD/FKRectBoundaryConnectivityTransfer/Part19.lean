/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part21
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryInitialState_reachable_iff (W : Nat)
    (u v : Bool × Fin W) :
    (fkRectBoundaryInitialState W).Reachable u v ↔ u.2 = v.2 := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | cons hadj p ih => exact hadj.1.trans ih
  · intro hcoord
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      exact ⟨hcoord, fun hbool => huv (Prod.ext hbool hcoord)⟩

theorem fkRectBoundaryInitialState_isConnectivity (W : Nat) :
    (fkRectBoundaryInitialState W).IsConnectivity := by
  intro u v
  rw [fkRectBoundaryInitialState_reachable_iff]
  constructor
  · intro h
    exact ⟨fun huv => (fkRectBoundaryInitialState W).loopless.irrefl u
      (huv ▸ h), h.1⟩
  · rintro ⟨huv, hcoord⟩
    exact ⟨hcoord, fun hbool => huv (Prod.ext hbool hcoord)⟩


end
end StatMech.FrontierD
