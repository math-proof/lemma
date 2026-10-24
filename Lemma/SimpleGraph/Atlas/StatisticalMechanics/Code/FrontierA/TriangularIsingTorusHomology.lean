import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusHomology
open StatMech StatMech.FrontierA


/--
[triangularTorusSurfaceEdgeClass_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusHomology.lean)
-/
@[path]
private lemma triangularTorusSurfaceEdgeClass_diag_eq
  {L : Nat}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L} :
-- imply
  triangularTorusSurfaceEdgeClass L s(v, v) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSurfaceEdgeClass_diag L v

/--
[triangularTorus_surfaceSubgraphHomology_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusHomology.lean)
-/
@[path]
private lemma triangularTorus_surfaceSubgraphHomology_eq_eq
  {L : Nat}
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) F = (fun _ => (triangularTorusEvenHomology L F).1, fun _ => (triangularTorusEvenHomology L F).2) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_surfaceSubgraphHomology_eq L F

/--
[triangularTorus_surfaceParitySign_eq_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusHomology.lean)
-/
@[path]
private lemma triangularTorus_surfaceParitySign_eq_spinCharacter_eq
  {a b : Fin 2}
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  surfaceParitySign (surfaceQuadraticParity (triangularTorusSurfaceSpin a b) (fun _ => h.1, fun _ => h.2)) = ons_spinCharacter a b h := by
-- proof
  apply StatMech.FrontierA.triangularTorus_surfaceParitySign_eq_spinCharacter a b h

/--
[triangularTorus_surfaceQuadraticEvenPolynomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusHomology.lean)
-/
@[path]
private lemma triangularTorus_surfaceQuadraticEvenPolynomial_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Complex}
  {a b : Fin 2} :
-- imply
  surfaceQuadraticEvenPolynomial (triangularTorusGraph L) (triangularTorusSurfaceEdgeClass L) (triangularTorusSurfaceSpin a b) weight = triangularTorusWeightedSpinCharacterSum L weight a b := by
-- proof
  apply StatMech.FrontierA.triangularTorus_surfaceQuadraticEvenPolynomial_eq L weight a b


-- created on 2026-10-23
