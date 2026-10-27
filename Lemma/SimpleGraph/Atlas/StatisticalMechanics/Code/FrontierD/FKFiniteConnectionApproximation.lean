import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKFiniteConnectionApproximation
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierD


/--
[exists_freeBox_twoPoint_gt_infinite_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFiniteConnectionApproximation.lean)
-/
@[path]
private lemma exists_freeBox_twoPoint_gt_infinite_sub_eq
  {d : Nat}
  {p q : Real}
  {x y : Site d}
  {epsilon : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ (m : Nat) (hx : x ∈ box d m) (hy : y ∈ box d m), (FK.freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real {omega | StatMech.Lattice.Connected d omega x y} - epsilon < FK.twoPointFun (FK.boxGraph d m) p q (⟨x, hx⟩ : FK.boxVerts d m) ⟨y, hy⟩ := by
-- proof
  apply StatMech.FrontierD.exists_freeBox_twoPoint_gt_infinite_sub hp hp1 hq x y hepsilon

/--
[exists_criticalFreeBox_exactDiagonalTwoPoint_gt_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFiniteConnectionApproximation.lean)
-/
@[path]
private lemma exists_criticalFreeBox_exactDiagonalTwoPoint_gt_sub_eq
  {q : Real}
  {scale : Nat}
  {epsilon : Real}
-- given
  (hq : 4 < q)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ (m : Nat) (hx : origin 2 ∈ box 2 m) (hy : fkQgt4ExactDiagonalSite (scale + 1) ∈ box 2 m), fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon < FK.twoPointFun (FK.boxGraph 2 m) (fkRectCriticalP q) q (⟨origin 2, hx⟩ : FK.boxVerts 2 m) ⟨fkQgt4ExactDiagonalSite (scale + 1), hy⟩ := by
-- proof
  apply StatMech.FrontierD.exists_criticalFreeBox_exactDiagonalTwoPoint_gt_sub hq scale hepsilon


-- created on 2026-10-23
