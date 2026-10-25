import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFiniteDualComparison
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexBrickInnerTriangleGraph_eq_triangularBoxGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFiniteDualComparison.lean)
-/
@[path]
private lemma triHexBrickInnerTriangleGraph_eq_triangularBoxGraph_eq
  {N : Nat} :
-- imply
  triHexBrickInnerTriangleGraph N = triangularBoxGraph N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInnerTriangleGraph_eq_triangularBoxGraph N

/--
[triHexBrickInnerBoundary_iff_shell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFiniteDualComparison.lean)
-/
@[path]
private lemma triHexBrickInnerBoundary_iff_shell_eq
  {N : Nat}
  {x : TriangularBoxVertex N} :
-- imply
  triHexBrickInnerBoundary N x ↔ x ∈ triangularBoxShell N N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInnerBoundary_iff_shell N x

/--
[triHexBrickInnerBoundaryGraph_eq_triangularBoxBoundaryGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFiniteDualComparison.lean)
-/
@[path]
private lemma triHexBrickInnerBoundaryGraph_eq_triangularBoxBoundaryGraph_eq
  {N : Nat} :
-- imply
  boundaryCliqueGraph (triHexBrickInnerBoundary N) = triangularBoxBoundaryGraph N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrickInnerBoundaryGraph_eq_triangularBoxBoundaryGraph N

/--
[triHexBrick_freeStarDual_inner_dominated_wiredTriangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFiniteDualComparison.lean)
-/
@[path]
private lemma triHexBrick_freeStarDual_inner_dominated_wiredTriangular_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V), A.indicator (fun _ => (1 : Real)) (triHexBrickDualInnerActiveRestrict hNm (triHexBrickPfdSupport m omega)) * fkProb (triHexPlanarFiniteStarPlanar m).G p q omega) ≤ activeBCMean (triangularBoxGraph N) (boundaryCliqueGraph (triHexBrickInnerBoundary N)) (fun _ => dualParam p q) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_freeStarDual_inner_dominated_wiredTriangular hNm hN hp hp1 hq hA

/--
[triHexBrick_freeTriangular_dominated_freeStarDual_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFiniteDualComparison.lean)
-/
@[path]
private lemma triHexBrick_freeTriangular_dominated_freeStarDual_inner_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (triangularBoxGraph N) ⊥ (fun _ => dualParam p q) q (A.indicator fun _ => (1 : Real)) ≤ ∑ omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V), A.indicator (fun _ => (1 : Real)) (triHexBrickDualInnerActiveRestrict hNm (triHexBrickPfdSupport m omega)) * fkProb (triHexPlanarFiniteStarPlanar m).G p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_freeTriangular_dominated_freeStarDual_inner hNm hp hp1 hq hA


-- created on 2026-10-23
