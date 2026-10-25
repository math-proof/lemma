/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectRawHorizontalCrossingRepresentativeIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    (fkRectRawHorizontalCrossingRepresentativeIndices R eta).card =
      fkRectRawHorizontalCrossingClusterCount R eta := by
  classical
  unfold fkRectRawHorizontalCrossingRepresentativeIndices
  rw [Finset.card_image_of_injective]
  · rfl
  · exact fkRectRawHorizontalCrossingRepresentative_injective R eta

theorem fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
    (R : FKRectTorus) (eta : R.Configuration) :
    ∀ i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta,
      FKRectRawHorizontalCrossingSource R eta i := by
  classical
  intro i hi
  unfold fkRectRawHorizontalCrossingRepresentativeIndices at hi
  rw [Finset.mem_image] at hi
  rcases hi with ⟨C, _, rfl⟩
  exact fkRectRawHorizontalCrossingRepresentative_source R eta C


theorem eq_of_representativeIndices_of_component_eq
    (R : FKRectTorus) (eta : R.Configuration)
    {i j : Fin R.height}
    (hi : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta)
    (hj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta)
    (hcomponent :
      (fkRectOpenGraph R eta).connectedComponentMk
          (fkRectLeftColumn R, i) =
        (fkRectOpenGraph R eta).connectedComponentMk
          (fkRectLeftColumn R, j)) :
    i = j := by
  classical
  unfold fkRectRawHorizontalCrossingRepresentativeIndices at hi hj
  rw [Finset.mem_image] at hi hj
  rcases hi with ⟨C, _, rfl⟩
  rcases hj with ⟨D, _, rfl⟩
  have hCD : C = D := by
    apply Subtype.ext
    exact (fkRectRawHorizontalCrossingRepresentative_component R eta C).symm.trans
      (hcomponent.trans
        (fkRectRawHorizontalCrossingRepresentative_component R eta D))
  exact congrArg (fkRectRawHorizontalCrossingRepresentative R eta) hCD


theorem fkRectCutHorizontalCrossingClusterCount_eq_raw
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectCutHorizontalCrossingClusterCount R omega =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  rfl


end
end StatMech.FrontierD
