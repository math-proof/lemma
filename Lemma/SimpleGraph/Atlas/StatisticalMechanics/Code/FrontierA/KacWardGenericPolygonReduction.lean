import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
open StatMech StatMech.FrontierA


/--
[kwFiniteSimplePolygonPhaseSign_of_genericCoordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericPolygonReduction.lean)
-/
@[path]
private lemma kwFiniteSimplePolygonPhaseSign_of_genericCoordinate_eq
-- given
  (hgeneric : KWGenericCoordinatePolygonPhaseSign) :
-- imply
  KWFiniteSimplePolygonPhaseSign := by
-- proof
  apply StatMech.FrontierA.kwFiniteSimplePolygonPhaseSign_of_genericCoordinate hgeneric


-- created on 2026-10-23
