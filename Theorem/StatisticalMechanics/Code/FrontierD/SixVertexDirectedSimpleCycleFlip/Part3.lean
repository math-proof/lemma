/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem SixVertexAtMostTwoCycleFamily.twoCycles_horizontalFlow
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint).horizontalFlow
        base =
      first.horizontalFlow base + second.horizontalFlow base := by
  unfold SixVertexAtMostTwoCycleFamily.horizontalFlow
  simp only [SixVertexAtMostTwoCycleFamily.twoCycles]
  change (∑ x : Fin 2, (![first, second] x).horizontalFlow base) = _
  rw [Fin.sum_univ_two]
  rfl

@[simp] theorem SixVertexAtMostTwoCycleFamily.twoCycles_verticalFlow
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail)
    (base : T.Vertex) :
    (SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint).verticalFlow
        base =
      first.verticalFlow base + second.verticalFlow base := by
  unfold SixVertexAtMostTwoCycleFamily.verticalFlow
  simp only [SixVertexAtMostTwoCycleFamily.twoCycles]
  change (∑ x : Fin 2, (![first, second] x).verticalFlow base) = _
  rw [Fin.sum_univ_two]
  rfl


theorem sixVertexDirectedSimpleCycles_flip_pair_related
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (omega eta : SixVertexArrows T)
    (hfirst : first.Follows omega) (hsecond : second.Follows eta)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (sixVertexTorusFlip first.mask omega,
        sixVertexTorusFlip second.mask eta) := by
  refine ⟨SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint,
    false, ?_, ?_⟩
  · funext base
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    rw [first.flip_horizontal_toNat omega hfirst,
      second.flip_horizontal_toNat eta hsecond]
    simp
    ring
  · funext base
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    rw [first.flip_vertical_toNat omega hfirst,
      second.flip_vertical_toNat eta hsecond]
    simp
    ring

end
end StatMech.FrontierD
