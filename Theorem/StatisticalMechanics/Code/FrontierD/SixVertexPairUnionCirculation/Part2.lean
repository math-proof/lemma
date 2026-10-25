/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPairUnionDelta_isCirculation
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (hsourceFirst : source.1.IceRule) (hsourceSecond : source.2.IceRule)
    (htargetFirst : target.1.IceRule) (htargetSecond : target.2.IceRule) :
    SixVertexTorusCirculation T
      (sixVertexPairUnionHorizontalDelta source target)
      (sixVertexPairUnionVerticalDelta source target) := by
  intro v
  have hsource := sixVertexPairUnion_isCirculation
    source hsourceFirst hsourceSecond v
  have htarget := sixVertexPairUnion_isCirculation
    target htargetFirst htargetSecond v
  unfold sixVertexPairUnionHorizontalDelta
    sixVertexPairUnionVerticalDelta
  omega

theorem sixVertexTorusCirculation_zero (T : EvenTorus) :
    SixVertexTorusCirculation T (fun _ => 0) (fun _ => 0) := by
  intro v
  simp

theorem SixVertexTorusCirculation.add
    {T : EvenTorus} {horizontal₁ vertical₁ horizontal₂ vertical₂ :
      T.Vertex -> Int}
    (hfirst : SixVertexTorusCirculation T horizontal₁ vertical₁)
    (hsecond : SixVertexTorusCirculation T horizontal₂ vertical₂) :
    SixVertexTorusCirculation T
      (fun v => horizontal₁ v + horizontal₂ v)
      (fun v => vertical₁ v + vertical₂ v) := by
  intro v
  have h₁ := hfirst v
  have h₂ := hsecond v
  change
    (horizontal₁ (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        horizontal₂ (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)) +
      (vertical₁ (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) +
        vertical₂ (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)) =
    (horizontal₁ v + horizontal₂ v) + (vertical₁ v + vertical₂ v)
  omega

theorem SixVertexTorusCirculation.neg
    {T : EvenTorus} {horizontal vertical : T.Vertex -> Int}
    (hcirculation : SixVertexTorusCirculation T horizontal vertical) :
    SixVertexTorusCirculation T (fun v => -horizontal v)
      (fun v => -vertical v) := by
  intro v
  have h := hcirculation v
  change
    -horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        -vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) =
      -horizontal v + -vertical v
  omega

theorem SixVertexTorusCirculation.sub
    {T : EvenTorus} {horizontal₁ vertical₁ horizontal₂ vertical₂ :
      T.Vertex -> Int}
    (hfirst : SixVertexTorusCirculation T horizontal₁ vertical₁)
    (hsecond : SixVertexTorusCirculation T horizontal₂ vertical₂) :
    SixVertexTorusCirculation T
      (fun v => horizontal₁ v - horizontal₂ v)
      (fun v => vertical₁ v - vertical₂ v) :=
  hfirst.add hsecond.neg


end
end StatMech.FrontierD
