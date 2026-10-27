import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
open StatMech StatMech.FrontierA


/--
[kwOrderedSplitEdges_surfaceSubgraphHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainHomology.lean)
-/
@[path]
private lemma kwOrderedSplitEdges_surfaceSubgraphHomology_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {edgeClass : Sym2 V → SurfaceHomology 1}
  {b : KWDartEdgeBits G}
  {y : KWPortChainField G}
-- given
  (hdiag : ∀ v, edgeClass s(v, v) = 0) :
-- imply
  surfaceSubgraphHomology (kwOrderedSplitEdgeClass edgeClass) (kwOrderedSplitEdges G order b y) = surfaceSubgraphHomology edgeClass (kwDartEdgeBitsFinset G b) := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplitEdges_surfaceSubgraphHomology G order edgeClass hdiag b y

/--
[surfaceQuadraticEvenPolynomial_eq_sum_actual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainHomology.lean)
-/
@[path]
private lemma surfaceQuadraticEvenPolynomial_eq_sum_actual_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {edgeClass : Sym2 V → SurfaceHomology 1}
  {lambda : SurfaceSpinStructure 1}
  {weight : Sym2 V → Complex} :
-- imply
  surfaceQuadraticEvenPolynomial G edgeClass lambda weight = ∑ F : KWActualEvenSubgraph G, (surfaceParitySign (surfaceQuadraticParity lambda (surfaceSubgraphHomology edgeClass F.1)) : Complex) * ∏ edge ∈ F.1, weight edge := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticEvenPolynomial_eq_sum_actual G edgeClass lambda weight

/--
[kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainHomology.lean)
-/
@[path]
private lemma kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {edgeClass : Sym2 V → SurfaceHomology 1}
  {lambda : SurfaceSpinStructure 1}
  {weight : Sym2 V → Complex}
-- given
  (hdiag : ∀ v, edgeClass s(v, v) = 0) :
-- imply
  surfaceQuadraticEvenPolynomial (kwOrderedDartPortSplitGraph G order) (kwOrderedSplitEdgeClass edgeClass) lambda (kwOrderedSplitWeight G weight) = surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
-- proof
  apply StatMech.FrontierA.kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq G order edgeClass hdiag lambda weight


-- created on 2026-10-23
