import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDualEvents
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkSquareBoxFaithfulDualPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean)
-/
@[path]
private lemma fkSquareBoxFaithfulDualPMF_apply_eq
  {n : Nat}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkSquareBoxFaithfulDualPMF n hp hp1 hq omega = ENNReal.ofReal (pfdDualProb (fkSquareBoxPlanar n) (dualParam p q) q omega) := by
-- proof
  apply StatMech.FrontierD.fkSquareBoxFaithfulDualPMF_apply n hp hp1 hq omega

/--
[fkSquareBox_fkPMF_eq_faithfulDualPMF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean)
-/
@[path]
private lemma fkSquareBox_fkPMF_eq_faithfulDualPMF_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq = fkSquareBoxFaithfulDualPMF n hp hp1 hq := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_fkPMF_eq_faithfulDualPMF n hp hp1 hq

/--
[fkSquareBox_eventProb_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean)
-/
@[path]
private lemma fkSquareBox_eventProb_duality_eq
  {n : Nat}
  {A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n)))}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq).toMeasure A = fkSquareBoxFaithfulDualEventProb n hp hp1 hq A := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_eventProb_duality n A hp hp1 hq

/--
[fkSquareBox_eventProb_selfDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFiniteDualEvents.lean)
-/
@[path]
private lemma fkSquareBox_eventProb_selfDual_eq
  {n : Nat}
  {A : Set (ConfigSpace (Sym2 (FK.boxVerts 2 n)))}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  (FK.fkPMF (FK.boxGraph 2 n) (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq).toMeasure A = fkSquareBoxFaithfulDualEventProb n (selfDualPoint_mem_Ioo hq).1 (selfDualPoint_mem_Ioo hq).2 hq A := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_eventProb_selfDual n A hq


-- created on 2026-10-23
