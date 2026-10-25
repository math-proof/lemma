/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectRawHorizontalCrossingSource
    (R : FKRectTorus) (eta : R.Configuration) :
    Fintype.card
        {y : Fin R.height // FKRectRawHorizontalCrossingSource R eta y} =
      fkRectRawHorizontalCrossingSourceCount R eta := by
  classical
  unfold fkRectRawHorizontalCrossingSourceCount
  rw [Fintype.card_subtype]

theorem fkRectRawHorizontalCrossingSourceCount_le_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawHorizontalCrossingSourceCount R eta ≤ R.height := by
  classical
  unfold fkRectRawHorizontalCrossingSourceCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem fkRectRawHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawHorizontalCrossingClusterCount R eta ≤
      fkRectRawHorizontalCrossingSourceCount R eta := by
  classical
  let G := fkRectOpenGraph R eta
  let Source := {y : Fin R.height //
    FKRectRawHorizontalCrossingSource R eta y}
  let Crossing := {C : G.ConnectedComponent //
    FKRectRawHorizontalCrossingComponent R eta C}
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
      fkRectRawHorizontalCrossingSourceCount R eta := by
    unfold Source fkRectRawHorizontalCrossingSourceCount
    exact Fintype.card_ofFinset
      (Finset.univ.filter fun y : Fin R.height =>
        FKRectRawHorizontalCrossingSource R eta y)
      (fun y => by
        constructor
        · intro hy
          exact (Finset.mem_filter.mp hy).2
        · intro hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
  rw [← hsourceCard]
  simpa [Crossing, fkRectRawHorizontalCrossingClusterCount] using hcard

theorem fkRectRawHorizontalCrossingClusterCount_le_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawHorizontalCrossingClusterCount R eta ≤ R.height :=
  (fkRectRawHorizontalCrossingClusterCount_le_sourceCount R eta).trans
    (fkRectRawHorizontalCrossingSourceCount_le_height R eta)


end
end StatMech.FrontierD
