/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectHorizontalCylinderCrossingRepresentativeIndices
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    (fkRectHorizontalCylinderCrossingRepresentativeIndices R rho).card =
      fkRectHorizontalCylinderCrossingClusterCount R rho := by
  classical
  unfold fkRectHorizontalCylinderCrossingRepresentativeIndices
  rw [Finset.card_image_of_injective]
  · rfl
  · exact fkRectHorizontalCylinderCrossingRepresentative_injective R rho

theorem fkRectHorizontalCylinderCrossingRepresentativeIndices_subset_sources
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    ∀ x ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho,
      FKRectHorizontalCylinderCrossingSource R rho x := by
  classical
  intro x hx
  unfold fkRectHorizontalCylinderCrossingRepresentativeIndices at hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨C, _, rfl⟩
  exact fkRectHorizontalCylinderCrossingRepresentative_source R rho C

theorem eq_of_horizontalCylinder_representatives_of_component_eq
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    {x y : Fin R.width}
    (hx : x ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho)
    (hy : y ∈ fkRectHorizontalCylinderCrossingRepresentativeIndices R rho)
    (hcomponent :
      (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
          (x, fkRectBottomRow R) =
        (FK.openSub (fkRectHorizontalCylinderGraph R) rho).connectedComponentMk
          (y, fkRectBottomRow R)) :
    x = y := by
  classical
  unfold fkRectHorizontalCylinderCrossingRepresentativeIndices at hx hy
  rw [Finset.mem_image] at hx hy
  rcases hx with ⟨C, _, rfl⟩
  rcases hy with ⟨D, _, rfl⟩
  have hCD : C = D := by
    apply Subtype.ext
    exact (fkRectHorizontalCylinderCrossingRepresentative_component
      R rho C).symm.trans
        (hcomponent.trans
          (fkRectHorizontalCylinderCrossingRepresentative_component
            R rho D))
  exact congrArg
    (fkRectHorizontalCylinderCrossingRepresentative R rho) hCD


end
end StatMech.FrontierD
