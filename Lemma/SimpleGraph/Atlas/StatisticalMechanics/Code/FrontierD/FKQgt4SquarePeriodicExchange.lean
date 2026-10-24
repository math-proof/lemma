import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicExchange
open Finset Set SimpleGraph MeasureTheory StatMech StatMech.FrontierD


/--
[fkSquare_freeProbMean_eq_lumpedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicExchange.lean)
-/
@[path]
private lemma fkSquare_freeProbMean_eq_lumpedDual_eq
  {N m : Nat}
  {p q : Real}
  {F : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet → Real}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)), F (fkSquarePfdSupport m omega) * FK.fkProb (FK.boxGraph 2 m) p q omega) = ∑ rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet, F rho * activeBCProb (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m (dualParam p q)) q rho := by
-- proof
  apply StatMech.FrontierD.fkSquare_freeProbMean_eq_lumpedDual hNm hp hp1 hq F

/--
[fkSquare_freeFiniteMeasure_real_faceDualInnerEvent_eq_lumpedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicExchange.lean)
-/
@[path]
private lemma fkSquare_freeFiniteMeasure_real_faceDualInnerEvent_eq_lumpedDual_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (FK.freeFiniteMeasure 2 m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent N A) = activeBCMean (fkSquareBoxFullDualGraph m) ⊥ (fkSquareDualLumpedParam N m (dualParam p q)) q (fun rho => A.indicator (fun _ => (1 : Real)) (fkSquareDualInnerActiveRestrict hNm rho)) := by
-- proof
  apply StatMech.FrontierD.fkSquare_freeFiniteMeasure_real_faceDualInnerEvent_eq_lumpedDual hNm hp hp1 hq A

/--
[fkSquare_freeBufferedMeasure_real_faceDualInnerEvent_eq_lumpedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicExchange.lean)
-/
@[path]
private lemma fkSquare_freeBufferedMeasure_real_faceDualInnerEvent_eq_lumpedDual_eq
  {N n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
-- given
  (hNn : N < square.bufferedRadius n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (square.freeBufferedMeasure n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent N A) = activeBCMean (fkSquareBoxFullDualGraph (square.bufferedRadius n)) ⊥ (fkSquareDualLumpedParam N (square.bufferedRadius n) (dualParam p q)) q (fun rho => A.indicator (fun _ => (1 : Real)) (fkSquareDualInnerActiveRestrict hNn rho)) := by
-- proof
  apply StatMech.FrontierD.fkSquare_freeBufferedMeasure_real_faceDualInnerEvent_eq_lumpedDual hNn hp hp1 hq A


-- created on 2026-10-23
