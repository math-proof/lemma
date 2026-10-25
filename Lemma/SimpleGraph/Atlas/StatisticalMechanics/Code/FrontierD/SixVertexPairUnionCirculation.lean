import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part6
open StatMech StatMech.FrontierD


/--
[sixVertexFlowConservation_of_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexFlowConservation_of_ice_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule) :
-- imply
  ((omega.horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)).toNat : Int) + (omega.vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)).toNat = (omega.horizontal v).toNat + (omega.vertical v).toNat := by
-- proof
  apply StatMech.FrontierD.sixVertexFlowConservation_of_ice omega homega v

/--
[sixVertexPairUnion_isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexPairUnion_isCirculation_eq
  {T : EvenTorus}
  {pair : SixVertexArrows T × SixVertexArrows T}
-- given
  (hfirst : pair.1.IceRule)
  (hsecond : pair.2.IceRule) :
-- imply
  SixVertexTorusCirculation T (sixVertexPairUnionHorizontal pair) (sixVertexPairUnionVertical pair) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairUnion_isCirculation pair hfirst hsecond

/--
[sixVertexPairUnionDelta_isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexPairUnionDelta_isCirculation_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hsourceFirst : source.1.IceRule)
  (hsourceSecond : source.2.IceRule)
  (htargetFirst : target.1.IceRule)
  (htargetSecond : target.2.IceRule) :
-- imply
  SixVertexTorusCirculation T (sixVertexPairUnionHorizontalDelta source target) (sixVertexPairUnionVerticalDelta source target) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairUnionDelta_isCirculation source target hsourceFirst hsourceSecond htargetFirst htargetSecond

/--
[sixVertexTorusCirculation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexTorusCirculation_zero_eq
  {T : EvenTorus} :
-- imply
  SixVertexTorusCirculation T (fun _ => 0) (fun _ => 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusCirculation_zero T

/--
[SixVertexTorusCirculation.add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma add_eq
  {T : EvenTorus}
  {horizontal₁ vertical₁ horizontal₂ vertical₂ : T.Vertex -> Int}
-- given
  (hfirst : SixVertexTorusCirculation T horizontal₁ vertical₁)
  (hsecond : SixVertexTorusCirculation T horizontal₂ vertical₂) :
-- imply
  SixVertexTorusCirculation T (fun v => horizontal₁ v + horizontal₂ v) (fun v => vertical₁ v + vertical₂ v) := by
-- proof
  apply StatMech.FrontierD.SixVertexTorusCirculation.add hfirst hsecond

/--
[SixVertexTorusCirculation.neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma neg_eq
  {T : EvenTorus}
  {horizontal vertical : T.Vertex -> Int}
-- given
  (hcirculation : SixVertexTorusCirculation T horizontal vertical) :
-- imply
  SixVertexTorusCirculation T (fun v => -horizontal v) (fun v => -vertical v) := by
-- proof
  apply StatMech.FrontierD.SixVertexTorusCirculation.neg hcirculation

/--
[SixVertexTorusCirculation.sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sub_eq
  {T : EvenTorus}
  {horizontal₁ vertical₁ horizontal₂ vertical₂ : T.Vertex -> Int}
-- given
  (hfirst : SixVertexTorusCirculation T horizontal₁ vertical₁)
  (hsecond : SixVertexTorusCirculation T horizontal₂ vertical₂) :
-- imply
  SixVertexTorusCirculation T (fun v => horizontal₁ v - horizontal₂ v) (fun v => vertical₁ v - vertical₂ v) := by
-- proof
  apply StatMech.FrontierD.SixVertexTorusCirculation.sub hfirst hsecond

/--
[sixVertexHorizontalWindingCirculation_isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexHorizontalWindingCirculation_isCirculation_eq
  {T : EvenTorus}
  {row : Fin T.height}
  {coefficient : Int} :
-- imply
  SixVertexTorusCirculation T (sixVertexHorizontalWindingCirculation row coefficient).1 (sixVertexHorizontalWindingCirculation row coefficient).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalWindingCirculation_isCirculation row coefficient

/--
[sixVertexVerticalWindingCirculation_isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexVerticalWindingCirculation_isCirculation_eq
  {T : EvenTorus}
  {column : Fin T.width}
  {coefficient : Int} :
-- imply
  SixVertexTorusCirculation T (sixVertexVerticalWindingCirculation column coefficient).1 (sixVertexVerticalWindingCirculation column coefficient).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexVerticalWindingCirculation_isCirculation column coefficient

/--
[sixVertexPlaquetteBoundaryCirculation_isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexPlaquetteBoundaryCirculation_isCirculation_eq
  {T : EvenTorus}
  {cell : T.Vertex}
  {coefficient : Int} :
-- imply
  SixVertexTorusCirculation T (sixVertexPlaquetteBoundaryCirculation cell coefficient).1 (sixVertexPlaquetteBoundaryCirculation cell coefficient).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexPlaquetteBoundaryCirculation_isCirculation cell coefficient

/--
[sixVertexTorusCirculation_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexTorusCirculation_sum_eq
  {T : EvenTorus}
  [Fintype Index]
-- given
  (horizontal vertical : Index -> T.Vertex -> Int)
  (hcirculation : forall index, SixVertexTorusCirculation T (horizontal index) (vertical index)) :
-- imply
  SixVertexTorusCirculation T (fun v => ∑ index, horizontal index v) (fun v => ∑ index, vertical index v) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusCirculation_sum horizontal vertical hcirculation

/--
[sixVertexGeneratedCycleCombination_isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean)
-/
@[path]
private lemma sixVertexGeneratedCycleCombination_isCirculation_eq
  {T : EvenTorus}
-- given
  (plaquetteWeight : T.Vertex -> Int)
  (horizontalWindingWeight : Fin T.height -> Int)
  (verticalWindingWeight : Fin T.width -> Int) :
-- imply
  SixVertexTorusCirculation T (sixVertexGeneratedCycleCombination T plaquetteWeight horizontalWindingWeight verticalWindingWeight).1 (sixVertexGeneratedCycleCombination T plaquetteWeight horizontalWindingWeight verticalWindingWeight).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexGeneratedCycleCombination_isCirculation T plaquetteWeight horizontalWindingWeight verticalWindingWeight


-- created on 2026-10-23
