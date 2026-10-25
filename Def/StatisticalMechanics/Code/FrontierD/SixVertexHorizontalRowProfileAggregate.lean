/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalActualDeficitRowProfileEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    {source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight //
      sixVertexHorizontalActualDeficitRowProfile source = rowProfile} ≃
      Sigma fun horizontal :
          SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
        Fin (sixVertexHorizontalProfileDeficit
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1)) where
  toFun source := by
    let horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile :=
      ⟨sixVertexHorizontalActualDeficitPair source.1,
        sixVertexHorizontalActualDeficitPair_bigrade source.1,
        source.2⟩
    refine ⟨horizontal, source.1.2.2.1, ?_⟩
    have hprofile := source.1.2.1.2
    simpa [horizontal, sixVertexHorizontalActualDeficitPair,
      hprofile] using source.1.2.2.2
  invFun target := by
    let horizontal := target.1
    let profile := sixVertexHorizontalPairCompletionProfile T horizontal.1
    let source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight :=
      ⟨profile,
        (⟨⟨horizontal.1, horizontal.2.1⟩, rfl⟩, target.2)⟩
    refine ⟨source, ?_⟩
    simpa [source, horizontal,
      sixVertexHorizontalActualDeficitRowProfile,
      sixVertexHorizontalActualDeficitPair] using horizontal.2.2
  left_inv source := by
    apply Subtype.ext
    rcases source with ⟨⟨profile, ⟨horizontal, hprofile⟩, index⟩, hrow⟩
    dsimp only
    subst profile
    rfl
  right_inv target := by
    rcases target with ⟨horizontal, index⟩
    rfl

noncomputable def sixVertexHorizontalActualSurplusRowProfileEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    {target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight //
      sixVertexHorizontalActualSurplusRowProfile target = rowProfile} ≃
      Sigma fun horizontal :
          SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
        Fin (sixVertexHorizontalProfileSurplus
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1)) where
  toFun target := by
    let horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile :=
      ⟨sixVertexHorizontalActualSurplusPair target.1,
        sixVertexHorizontalActualSurplusPair_bigrade target.1,
        target.2⟩
    refine ⟨horizontal, target.1.2.2.1, ?_⟩
    have hprofile := target.1.2.1.2
    simpa [horizontal, sixVertexHorizontalActualSurplusPair,
      hprofile] using target.1.2.2.2
  invFun source := by
    let horizontal := source.1
    let profile := sixVertexHorizontalPairCompletionProfile T horizontal.1
    let target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight :=
      ⟨profile,
        (⟨⟨horizontal.1, horizontal.2.1⟩, rfl⟩, source.2)⟩
    refine ⟨target, ?_⟩
    simpa [target, horizontal,
      sixVertexHorizontalActualSurplusRowProfile,
      sixVertexHorizontalActualSurplusPair] using horizontal.2.2
  left_inv target := by
    apply Subtype.ext
    rcases target with ⟨⟨profile, ⟨horizontal, hprofile⟩, index⟩, hrow⟩
    dsimp only
    subst profile
    rfl
  right_inv source := by
    rcases source with ⟨horizontal, index⟩
    rfl

end
end StatMech.FrontierD
