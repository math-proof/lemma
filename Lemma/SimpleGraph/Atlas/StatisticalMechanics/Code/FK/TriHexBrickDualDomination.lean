import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexBrickDualDomination
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexBrick_freeTriangular_dominated_lumped_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualDomination.lean)
-/
@[path]
private lemma triHexBrick_freeTriangular_dominated_lumped_inner_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (triHexBrickInnerTriangleGraph N) ⊥ (fun _ => p) q (A.indicator fun _ => (1 : Real)) ≤ activeBCMean (triHexBrickFullDualGraph m) ⊥ (triHexBrickDualLumpedParam N m p) q (fun rho => A.indicator (fun _ => (1 : Real)) (triHexBrickDualInnerActiveRestrict hNm rho)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_freeTriangular_dominated_lumped_inner hNm hp hp1 hq hA

/--
[triHexBrick_lumped_inner_dominated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualDomination.lean)
-/
@[path]
private lemma triHexBrick_lumped_inner_dominated_wired_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (triHexBrickFullDualGraph m) ⊥ (triHexBrickDualLumpedParam N m p) q (fun rho => A.indicator (fun _ => (1 : Real)) (triHexBrickDualInnerActiveRestrict hNm rho)) ≤ activeBCMean (triHexBrickInnerTriangleGraph N) (boundaryCliqueGraph (triHexBrickInnerBoundary N)) (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_lumped_inner_dominated_wired hNm hN hp hp1 hq hA

/--
[triHexBrick_pfdDual_inner_dominated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualDomination.lean)
-/
@[path]
private lemma triHexBrick_pfdDual_inner_dominated_wired_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V), A.indicator (fun _ => (1 : Real)) (triHexBrickDualInnerActiveRestrict hNm (triHexBrickPfdSupport m omega)) * pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega) ≤ activeBCMean (triHexBrickInnerTriangleGraph N) (boundaryCliqueGraph (triHexBrickInnerBoundary N)) (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_pfdDual_inner_dominated_wired hNm hN hp hp1 hq hA

/--
[triHexBrick_freeTriangular_dominated_pfdDual_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualDomination.lean)
-/
@[path]
private lemma triHexBrick_freeTriangular_dominated_pfdDual_inner_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (triHexBrickInnerTriangleGraph N) ⊥ (fun _ => p) q (A.indicator fun _ => (1 : Real)) ≤ ∑ omega : ConfigSpace (Sym2 (triHexPlanarFiniteStarPlanar m).V), A.indicator (fun _ => (1 : Real)) (triHexBrickDualInnerActiveRestrict hNm (triHexBrickPfdSupport m omega)) * pfdDualProb (triHexPlanarFiniteStarPlanar m) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexBrick_freeTriangular_dominated_pfdDual_inner hNm hp hp1 hq hA


-- created on 2026-10-23
