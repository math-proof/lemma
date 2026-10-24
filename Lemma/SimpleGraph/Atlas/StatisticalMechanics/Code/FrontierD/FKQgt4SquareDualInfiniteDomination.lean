import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualInfiniteDomination
open Filter Finset MeasureTheory Set SimpleGraph Topology StatMech StatMech.FrontierD


/--
[continuous_fkSquareFaceDualInnerActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma continuous_fkSquareFaceDualInnerActive_eq
  {N : Nat} :
-- imply
  Continuous (fkSquareFaceDualInnerActive N) := by
-- proof
  apply StatMech.FrontierD.continuous_fkSquareFaceDualInnerActive N

/--
[isClopen_fkSquareFaceDualInnerEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma isClopen_fkSquareFaceDualInnerEvent_eq
  {N : Nat}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)} :
-- imply
  IsClopen (fkSquareFaceDualInnerEvent N A) := by
-- proof
  apply StatMech.FrontierD.isClopen_fkSquareFaceDualInnerEvent N A

/--
[measurableSet_fkSquareFaceDualInnerEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma measurableSet_fkSquareFaceDualInnerEvent_eq
  {N : Nat}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)} :
-- imply
  MeasurableSet (fkSquareFaceDualInnerEvent N A) := by
-- proof
  apply StatMech.FrontierD.measurableSet_fkSquareFaceDualInnerEvent N A

/--
[freeFiniteMeasure_real_faceDualInnerEvent_eq_pfd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_faceDualInnerEvent_eq_pfd_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hself : dualParam p q = p) :
-- imply
  (FK.freeFiniteMeasure 2 m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent N A) = ∑ omega : ConfigSpace (Sym2 (FK.boxVerts 2 m)), A.indicator (fun _ => (1 : Real)) (fkSquareDualInnerActiveRestrict hNm (fkSquarePfdSupport m omega)) * pfdDualProb (fkSquareBoxPlanar m) p q omega := by
-- proof
  apply StatMech.FrontierD.freeFiniteMeasure_real_faceDualInnerEvent_eq_pfd hNm hp hp1 hq hself A

/--
[activeBCMean_wired_eq_wiredFiniteMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma activeBCMean_wired_eq_wiredFiniteMeasure_eq
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeBCMean (FK.boxGraph 2 N) (boundaryCliqueGraph (FK.boxBoundary 2 N)) (fun _ => p) q (A.indicator fun _ => (1 : Real)) = (FK.wiredFiniteMeasure 2 N hp hp1 hq : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 N ⁻¹' (restrictActive (FK.boxGraph 2 N) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.activeBCMean_wired_eq_wiredFiniteMeasure N hp hp1 hq A

/--
[freeFinite_faceDual_le_wiredFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma freeFinite_faceDual_le_wiredFinite_eq
  {R N m : Nat}
  {q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
-- given
  (hRN : R ≤ N)
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (FK.freeFiniteMeasure 2 m (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent R A) ≤ (FK.wiredFiniteMeasure 2 N (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 R ⁻¹' (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.freeFinite_faceDual_le_wiredFinite hRN hNm hN hq hA

/--
[criticalFree_faceDual_cylinder_le_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean)
-/
@[path]
private lemma criticalFree_faceDual_cylinder_le_wired_eq
  {R : Nat}
  {q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
-- given
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (FK.freeInfiniteVolume 2 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent R A) ≤ (FK.wiredInfiniteVolume 2 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 R ⁻¹' (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.criticalFree_faceDual_cylinder_le_wired R hq hA


-- created on 2026-10-23
