import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode
open StatMech StatMech.FrontierD


/--
[sixVertexDirectedTorusEdgeOfArrow_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdgeOfArrow_physical_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {edge : SixVertexTorusEdge T} :
-- imply
  (sixVertexDirectedTorusEdgeOfArrow omega edge).physical = sixVertexTorusEdgePhysical edge := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdgeOfArrow_physical omega edge

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveSeamEdge_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma nextPositiveSeamEdge_shape_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  (seed.nextPositiveSeamEdge hsame).1 = 1 ∧ (seed.nextPositiveSeamEdge hsame).2.2 = svFinLast T.height_pos := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveSeamEdge_shape seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_nextPositiveSeamEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma firstSeamEdge_ne_nextPositiveSeamEdge_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  seed.firstSeamEdge ≠ seed.nextPositiveSeamEdge hsame := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_nextPositiveSeamEdge seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.canonicalWindingColumns_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma canonicalWindingColumns_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  seed.firstWindingColumn ≠ seed.nextPositiveWindingColumn hsame := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.canonicalWindingColumns_ne seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_first_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma sameStrandArcPair_first_physical_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  ((seed.sameStrandArcPair hsame).first.edge (seed.sameStrandArcPair hsame).first.firstIndex).physical = sixVertexTorusEdgePhysical seed.firstSeamEdge := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_first_physical seed hsame

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_second_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma sameStrandArcPair_second_physical_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed.first seed.second) :
-- imply
  ((seed.sameStrandArcPair hsame).second.edge (seed.sameStrandArcPair hsame).second.firstIndex).physical = sixVertexTorusEdgePhysical (seed.nextPositiveSeamEdge hsame) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_second_physical seed hsame

/--
[sixVertexDecodeVerticalPhysicalEdge_leftInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma sixVertexDecodeVerticalPhysicalEdge_leftInverse_eq
  {T : EvenTorus}
  {edge : SixVertexTorusEdge T}
-- given
  (hvertical : edge.1 = 1) :
-- imply
  sixVertexDecodeVerticalPhysicalEdge (sixVertexTorusEdgePhysical edge) = edge := by
-- proof
  apply StatMech.FrontierD.sixVertexDecodeVerticalPhysicalEdge_leftInverse edge hvertical

/--
[SixVertexCanonicalSameStrandCutCode.decodeSeamPair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma decodeSeamPair_eq_eq
  {T : EvenTorus}
  {code : SixVertexCanonicalSameStrandCutCode T} :
-- imply
  code.decodeSeamPair = (code.firstSeamEdge, code.secondSeamEdge) := by
-- proof
  apply StatMech.FrontierD.SixVertexCanonicalSameStrandCutCode.decodeSeamPair_eq code

/--
[SixVertexCanonicalSameStrandCutCode.seamPair_eq_of_arcs_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean)
-/
@[path]
private lemma seamPair_eq_of_arcs_eq_eq
  {T : EvenTorus}
  {first second : SixVertexCanonicalSameStrandCutCode T}
-- given
  (harcs : first.arcs = second.arcs) :
-- imply
  (first.firstSeamEdge, first.secondSeamEdge) = (second.firstSeamEdge, second.secondSeamEdge) := by
-- proof
  apply StatMech.FrontierD.SixVertexCanonicalSameStrandCutCode.seamPair_eq_of_arcs_eq first second harcs


-- created on 2026-10-23
