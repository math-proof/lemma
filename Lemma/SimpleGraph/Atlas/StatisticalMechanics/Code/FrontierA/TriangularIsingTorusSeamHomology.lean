import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSeamHomology
open StatMech StatMech.FrontierA


/--
[triangularTorusXSeamEdge_dart_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSeamHomology.lean)
-/
@[path]
private lemma triangularTorusXSeamEdge_dart_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : triangularTorusDart L} :
-- imply
  triangularTorusXSeamEdge L (triangularTorusDartEquiv L d).edge ↔ ons_xWrap (triangularTorusXMovementDart L d) := by
-- proof
  apply StatMech.FrontierA.triangularTorusXSeamEdge_dart_iff L d

/--
[triangularTorusYSeamEdge_dart_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSeamHomology.lean)
-/
@[path]
private lemma triangularTorusYSeamEdge_dart_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : triangularTorusDart L} :
-- imply
  triangularTorusYSeamEdge L (triangularTorusDartEquiv L d).edge ↔ ons_yWrap (triangularTorusYMovementDart L d) := by
-- proof
  apply StatMech.FrontierA.triangularTorusYSeamEdge_dart_iff L d

/--
[triangularTorusSpinDartSeamSign_eq_surfaceHomologyCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSeamHomology.lean)
-/
@[path]
private lemma triangularTorusSpinDartSeamSign_eq_surfaceHomologyCharacter_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : triangularTorusDart L} :
-- imply
  triangularTorusSpinDartSeamSign L a b d = surfaceHomologyCharacter (fun _ => a, fun _ => b) (triangularTorusSurfaceEdgeClass L (triangularTorusDartEquiv L d).edge) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSpinDartSeamSign_eq_surfaceHomologyCharacter L a b d


-- created on 2026-10-23
