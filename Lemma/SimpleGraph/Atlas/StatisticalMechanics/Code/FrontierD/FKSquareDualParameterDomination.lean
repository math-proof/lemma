import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKSquareDualParameterDomination
open Filter Finset MeasureTheory Set SimpleGraph Topology StatMech StatMech.FrontierD


/--
[freeFinite_faceDual_le_wiredFinite_dualParam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKSquareDualParameterDomination.lean)
-/
@[path]
private lemma freeFinite_faceDual_le_wiredFinite_dualParam_eq
  {R N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
-- given
  (hRN : R ≤ N)
  (hNm : N < m)
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (FK.freeFiniteMeasure 2 m hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent R A) ≤ (FK.wiredFiniteMeasure 2 N (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 R ⁻¹' (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.freeFinite_faceDual_le_wiredFinite_dualParam hRN hNm hN hp hp1 hq hA

/--
[freeInfinite_faceDual_cylinder_le_wired_dualParam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKSquareDualParameterDomination.lean)
-/
@[path]
private lemma freeInfinite_faceDual_cylinder_le_wired_dualParam_eq
  {R : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent R A) ≤ (FK.wiredInfiniteVolume 2 (dualParam_pos hp hp1 (zero_lt_one.trans_le hq)) (dualParam_lt_one hp hp1 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 R ⁻¹' (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.freeInfinite_faceDual_cylinder_le_wired_dualParam R hp hp1 hq hA


-- created on 2026-10-23
