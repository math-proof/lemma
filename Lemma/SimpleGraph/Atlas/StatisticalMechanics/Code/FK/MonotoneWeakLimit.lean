import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[fkWiredLimit_isIncreasing_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fkWiredLimit_isIncreasing_preimage_eq
  {d : ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hS : IsIncreasing S) :
-- imply
  IsIncreasing (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkWiredLimit_isIncreasing_preimage N hS

/--
[fkWiredLimit_isClopen_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fkWiredLimit_isClopen_preimage_eq
  {d : ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} :
-- imply
  IsClopen (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkWiredLimit_isClopen_preimage N S

/--
[fkWiredLimit_measurableSet_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fkWiredLimit_measurableSet_preimage_eq
  {d : ℕ}
  {N : ℕ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} :
-- imply
  MeasurableSet (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkWiredLimit_measurableSet_preimage N S

/--
[fkWiredLimit_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fkWiredLimit_succ_le_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (wiredFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkWiredLimit_succ_le N m hNm hp hp1 hS

/--
[fkWiredLimit_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fkWiredLimit_antitone_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Antitone (fun k => (wiredFiniteMeasure d (N+k) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) := by
-- proof
  apply StatMech.FK.fkWiredLimit_antitone N hp hp1 hS

/--
[fk_wired_limit_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fk_wired_limit_exists_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 (fkWiredLimitValue N hp hp1 S)) := by
-- proof
  apply StatMech.FK.fk_wired_limit_exists N hp hp1 hS

/--
[fk_wired_limit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fk_wired_limit_le_eq
  {d : ℕ}
  {N m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fkWiredLimitValue N hp hp1 S ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fk_wired_limit_le N m hNm hp hp1 S

/--
[fkWiredLimit_wiredInfiniteVolume_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fkWiredLimit_wiredInfiniteVolume_eq_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) = fkWiredLimitValue N hp hp1 S := by
-- proof
  apply StatMech.FK.fkWiredLimit_wiredInfiniteVolume_eq N hp hp1 hS

/--
[fk_wired_infinite_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonotoneWeakLimit.lean)
-/
@[path]
private lemma fk_wired_infinite_measure_eq
  {d : ℕ}
  {N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S)) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S))) := by
-- proof
  apply StatMech.FK.fk_wired_infinite_measure N hp hp1 hS


-- created on 2026-10-23
