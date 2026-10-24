import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusAngularSplit
open StatMech StatMech.FrontierA


/--
[triangularTorus_orderedSplit_surfaceQuadraticEvenPolynomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusAngularSplit.lean)
-/
@[path]
private lemma triangularTorus_orderedSplit_surfaceQuadraticEvenPolynomial_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {order : KWPortOrder (triangularTorusGraph L)}
  {weight : Sym2 (ZMod L × ZMod L) → Complex}
  {a b : Fin 2} :
-- imply
  surfaceQuadraticEvenPolynomial (kwOrderedDartPortSplitGraph (triangularTorusGraph L) order) (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) (triangularTorusSurfaceSpin a b) (kwOrderedSplitWeight (triangularTorusGraph L) weight) = triangularTorusWeightedSpinCharacterSum L weight a b := by
-- proof
  apply StatMech.FrontierA.triangularTorus_orderedSplit_surfaceQuadraticEvenPolynomial_eq L order weight a b


-- created on 2026-10-23
