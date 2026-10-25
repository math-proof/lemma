/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Def.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCutHorizontalCrossingSourceCount_le_height
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectCutHorizontalCrossingSourceCount R omega ≤ R.height := by
  classical
  unfold fkRectCutHorizontalCrossingSourceCount
  calc
    (Finset.univ.filter fun y : Fin R.height =>
        FKRectCutHorizontalCrossingSource R omega y).card ≤
        (Finset.univ : Finset (Fin R.height)).card :=
      Finset.card_filter_le _ _
    _ = R.height := by simp

theorem fkRectCutHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectCutHorizontalCrossingClusterCount R omega ≤
      fkRectCutHorizontalCrossingSourceCount R omega := by
  classical
  let G := fkRectOpenGraph R (fkRectForceCutClosed R omega)
  let Source := {y : Fin R.height //
    FKRectCutHorizontalCrossingSource R omega y}
  let Crossing := {C : G.ConnectedComponent //
    FKRectCutHorizontalCrossingComponent R omega C}
  let sourceComponent : Source → Crossing := fun y =>
    ⟨G.connectedComponentMk (fkRectLeftColumn R, y.1), by
      rcases y.2 with ⟨z, hyz⟩
      exact ⟨⟨y.1, rfl⟩,
        ⟨z, (SimpleGraph.ConnectedComponent.sound hyz).symm⟩⟩⟩
  have hsurj : Function.Surjective sourceComponent := by
    rintro ⟨C, ⟨⟨y, hy⟩, ⟨z, hz⟩⟩⟩
    have hyz : G.Reachable (fkRectLeftColumn R, y)
        (fkRectRightColumn R, z) :=
      SimpleGraph.ConnectedComponent.exact (hy.trans hz.symm)
    refine ⟨⟨y, ⟨z, hyz⟩⟩, ?_⟩
    apply Subtype.ext
    exact hy
  have hcard := Fintype.card_le_of_surjective sourceComponent hsurj
  have hsourceCard : Fintype.card Source =
      fkRectCutHorizontalCrossingSourceCount R omega := by
    unfold Source fkRectCutHorizontalCrossingSourceCount
    exact Fintype.card_ofFinset
      (Finset.univ.filter fun y : Fin R.height =>
        FKRectCutHorizontalCrossingSource R omega y)
      (fun y => by
        constructor
        · intro hy
          exact (Finset.mem_filter.mp hy).2
        · intro hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
  rw [← hsourceCard]
  simpa [Crossing, fkRectCutHorizontalCrossingClusterCount] using hcard


end
end StatMech.FrontierD
