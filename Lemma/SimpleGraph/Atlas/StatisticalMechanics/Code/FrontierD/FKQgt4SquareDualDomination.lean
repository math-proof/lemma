import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualDomination
open Finset Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkSquare_lumped_inner_dominated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualDomination.lean)
-/
@[path]
private lemma fkSquare_lumped_inner_dominated_wired_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m p) q (fun rho => A.indicator (fun _ => (1 : Real)) (fkSquareDualInnerActiveRestrict hNm rho)) ≤ activeBCMean (FK.boxGraph 2 N) (boundaryCliqueGraph (FK.boxBoundary 2 N)) (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FrontierD.fkSquare_lumped_inner_dominated_wired hNm hN hp hp1 hq hA

/--
[fkSquare_pfdDual_inner_dominated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualDomination.lean)
-/
@[path]
private lemma fkSquare_pfdDual_inner_dominated_wired_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)), A.indicator (fun _ => (1 : Real)) (fkSquareDualInnerActiveRestrict hNm (fkSquarePfdSupport m omega)) * pfdDualProb (fkSquareBoxPlanar m) p q omega) ≤ activeBCMean (FK.boxGraph 2 N) (boundaryCliqueGraph (FK.boxBoundary 2 N)) (fun _ => p) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FrontierD.fkSquare_pfdDual_inner_dominated_wired hNm hN hp hp1 hq hA


-- created on 2026-10-23
