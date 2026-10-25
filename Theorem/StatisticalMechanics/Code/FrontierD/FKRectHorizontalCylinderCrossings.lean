/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut
    (R : FKRectTorus) (eta : FKRectHorizontalCutClosedConfig R) :
    fkRectHorizontalCylinderCrossingClusterCount R
        (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 =
      fkRectHorizontalCutPrimalCrossingClusterCount R eta.1 := by
  classical
  let G := FK.openSub (fkRectHorizontalCylinderGraph R)
    (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1
  let H := fkRectOpenGraph R eta.1
  have hGH : G = H := fkRectHorizontalCylinder_openSub_eq R eta
  have hrel : ∀ {x y : R.Vertex}, H.Adj x y ↔ G.Adj x y := by
    intro x y
    rw [hGH]
  let phi : G ≃g H := ⟨Equiv.refl R.Vertex, hrel⟩
  let e : G.ConnectedComponent ≃ H.ConnectedComponent :=
    phi.connectedComponentEquiv
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv e ?_
  intro C
  change FKRectHorizontalCylinderCrossingComponent R
      (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 C ↔
    FKRectHorizontalCutPrimalCrossingComponent R eta.1 (e C)
  unfold FKRectHorizontalCylinderCrossingComponent
    FKRectHorizontalCutPrimalCrossingComponent
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩
    · calc
        H.connectedComponentMk (x, fkRectBottomRow R) =
            e (G.connectedComponentMk (x, fkRectBottomRow R)) := by
              simp [e, phi]
        _ = e C := congrArg e hx
    · calc
        H.connectedComponentMk (y, fkRectTopRow R) =
            e (G.connectedComponentMk (y, fkRectTopRow R)) := by
              simp [e, phi]
        _ = e C := congrArg e hy
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩
    · apply e.injective
      simpa [e, phi] using hx
    · apply e.injective
      simpa [e, phi] using hy


theorem fkRectHorizontalCylinderCrossingClusterCount_force_eq
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectHorizontalCylinderCrossingClusterCount R
        (fkRectHorizontalCutClosedEdgeConfigEquiv R
          ⟨fkRectForceHorizontalCutClosed R omega,
            fkRectHorizontalCutClosedConfiguration_force R omega⟩).1 =
      fkRectHorizontalCutPrimalCrossingClusterCount R
        (fkRectForceHorizontalCutClosed R omega) :=
  fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut R _


theorem fkRectHorizontalCylinderCrossingTail_iff_horizontalCut
    (R : FKRectTorus) (eta : FKRectHorizontalCutClosedConfig R) (n : Nat) :
    n ≤ fkRectHorizontalCylinderCrossingClusterCount R
        (fkRectHorizontalCutClosedEdgeConfigEquiv R eta).1 ↔
      n ≤ fkRectHorizontalCutPrimalCrossingClusterCount R eta.1 := by
  rw [fkRectHorizontalCylinderCrossingClusterCount_eq_horizontalCut]


end
end StatMech.FrontierD
