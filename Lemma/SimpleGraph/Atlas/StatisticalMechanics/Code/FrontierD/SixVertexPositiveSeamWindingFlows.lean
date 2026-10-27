import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
open StatMech StatMech.FrontierD


/--
[sixVertexPositiveHorizontalWindingFamily_horizontalFlow_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma sixVertexPositiveHorizontalWindingFamily_horizontalFlow_same_eq
  {T : EvenTorus}
  {row : Fin T.height}
  {column : Fin T.width} :
-- imply
  (sixVertexPositiveHorizontalWindingFamily row).horizontalFlow (column, row) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHorizontalWindingFamily_horizontalFlow_same row column

/--
[sixVertexPositiveHorizontalWindingFamily_horizontalFlow_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma sixVertexPositiveHorizontalWindingFamily_horizontalFlow_other_eq
  {T : EvenTorus}
  {first second : Fin T.height}
  {column : Fin T.width}
-- given
  (hne : first ≠ second) :
-- imply
  (sixVertexPositiveHorizontalWindingFamily second).horizontalFlow (column, first) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHorizontalWindingFamily_horizontalFlow_other hne column

/--
[sixVertexPositiveVerticalWindingFamily_verticalFlow_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma sixVertexPositiveVerticalWindingFamily_verticalFlow_same_eq
  {T : EvenTorus}
  {column : Fin T.width}
  {row : Fin T.height} :
-- imply
  (sixVertexPositiveVerticalWindingFamily column).verticalFlow (column, row) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveVerticalWindingFamily_verticalFlow_same column row

/--
[sixVertexPositiveVerticalWindingFamily_verticalFlow_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma sixVertexPositiveVerticalWindingFamily_verticalFlow_other_eq
  {T : EvenTorus}
  {first second : Fin T.width}
  {row : Fin T.height}
-- given
  (hne : first ≠ second) :
-- imply
  (sixVertexPositiveVerticalWindingFamily second).verticalFlow (first, row) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveVerticalWindingFamily_verticalFlow_other hne row

/--
[sixVertexTorusEdgeSeamSign_eq_one_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma sixVertexTorusEdgeSeamSign_eq_one_shape_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {edge : SixVertexTorusEdge T}
-- given
  (h : sixVertexTorusEdgeSeamSign omega eta edge = 1) :
-- imply
  edge.1 = 1 ∧ edge.2.2 = svFinLast T.height_pos := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeSeamSign_eq_one_shape h

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma firstSeamEdge_shape_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.firstSeamEdge.1 = 1 ∧ seed.firstSeamEdge.2.2 = svFinLast T.height_pos := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_shape seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.secondSeamEdge_shape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma secondSeamEdge_shape_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.secondSeamEdge.1 = 1 ∧ seed.secondSeamEdge.2.2 = svFinLast T.height_pos := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.secondSeamEdge_shape seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_secondSeamEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma firstSeamEdge_ne_secondSeamEdge_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.firstSeamEdge ≠ seed.secondSeamEdge := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_secondSeamEdge seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.windingColumns_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma windingColumns_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.firstWindingColumn ≠ seed.secondWindingColumn := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.windingColumns_ne seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.windingFlows_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma windingFlows_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {row : Fin T.height} :
-- imply
  seed.firstWindingFamily.verticalFlow (seed.firstWindingColumn, row) ≠ seed.secondWindingFamily.verticalFlow (seed.firstWindingColumn, row) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.windingFlows_ne seed row

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.windingTargets_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamWindingFlows.lean)
-/
@[path]
private lemma windingTargets_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {source : SixVertexArrows T × SixVertexArrows T}
  {first : SixVertexSignedWindingCycleTarget source seed.firstWindingFamily true}
  {second : SixVertexSignedWindingCycleTarget source seed.secondWindingFamily true} :
-- imply
  first.target ≠ second.target := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.windingTargets_ne seed first second


-- created on 2026-10-23
