import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBufferedIdentification
open Finset Set MeasureTheory Filter Topology StatMech StatMech.FrontierD


/--
[fkSquarePeriodicConfigEquiv_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodicConfigEquiv_boxRestrict_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  fkSquarePeriodicConfigEquiv (square.bufferedRadius n) (FK.boxRestrict 2 (square.bufferedRadius n) omega) = square.bufferedRestrict n omega := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodicConfigEquiv_boxRestrict n omega

/--
[fkSquarePeriodicConfigEquiv_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodicConfigEquiv_monotone_eq
  {n : Nat} :
-- imply
  Monotone (fkSquarePeriodicConfigEquiv n) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodicConfigEquiv_monotone n

/--
[fkSquarePeriodic_freeBufferedMeasure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeBufferedMeasure_eq_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.freeBufferedMeasure n hp hp1 hq = FK.freeFiniteMeasure 2 (square.bufferedRadius n) hp hp1 hq := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeBufferedMeasure_eq n hp hp1 hq

/--
[fkSquarePeriodic_bufferedBoundary_iff_orbitBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_bufferedBoundary_iff_orbitBoundary_eq
  {n : Nat}
  {x : square.BufferedVertex n}
-- given
  (hr : 0 < square.bufferedRadius n) :
-- imply
  square.bufferedBoundary n x ↔ square.orbitBoundary (square.bufferedRadius n) x := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_bufferedBoundary_iff_orbitBoundary n hr x

/--
[fkSquarePeriodic_wiredBufferedMeasure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredBufferedMeasure_eq_eq
  {n : Nat}
  {p q : Real}
-- given
  (hr : 0 < square.bufferedRadius n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.wiredBufferedMeasure n hp hp1 hq = FK.wiredFiniteMeasure 2 (square.bufferedRadius n) hp hp1 hq := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredBufferedMeasure_eq n hr hp hp1 hq

/--
[fkSquarePeriodic_bufferedCylinder_eq_boxCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_bufferedCylinder_eq_boxCylinder_eq
  {n : Nat}
  {S : Set (ConfigSpace (Sym2 (square.BufferedVertex n)))} :
-- imply
  square.bufferedCylinder n S = FK.boxRestrict 2 (square.bufferedRadius n) ⁻¹' ((fkSquarePeriodicConfigEquiv (square.bufferedRadius n)) ⁻¹' S) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_bufferedCylinder_eq_boxCylinder n S

/--
[fkSquarePeriodic_freeBufferedInfiniteVolume_real_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeBufferedInfiniteVolume_real_cylinder_eq
  {N : Nat}
  {p q : Real}
  {S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) = (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeBufferedInfiniteVolume_real_cylinder N hp hp1 hq hS

/--
[fkSquarePeriodic_wiredBufferedInfiniteVolume_real_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredBufferedInfiniteVolume_real_cylinder_eq
  {N : Nat}
  {p q : Real}
  {S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) = (FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredBufferedInfiniteVolume_real_cylinder N hp hp1 hq hS

/--
[fkSquarePeriodic_freeBufferedInfiniteVolume_real_allCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeBufferedInfiniteVolume_real_allCylinder_eq
  {N : Nat}
  {p q : Real}
  {S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) = (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeBufferedInfiniteVolume_real_allCylinder N hp hp1 hq S

/--
[fkSquarePeriodic_wiredBufferedInfiniteVolume_real_allCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredBufferedInfiniteVolume_real_allCylinder_eq
  {N : Nat}
  {p q : Real}
  {S : Set (ConfigSpace (Sym2 (square.BufferedVertex N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) = (FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (square.bufferedCylinder N S) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredBufferedInfiniteVolume_real_allCylinder N hp hp1 hq S

/--
[fkSquarePeriodic_freeBufferedInfiniteVolume_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeBufferedInfiniteVolume_eq_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  square.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) = FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeBufferedInfiniteVolume_eq hp hp1 hq

/--
[fkSquarePeriodic_wiredBufferedInfiniteVolume_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareBufferedIdentification.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredBufferedInfiniteVolume_eq_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  square.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) = FK.wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredBufferedInfiniteVolume_eq hp hp1 hq


-- created on 2026-10-23
