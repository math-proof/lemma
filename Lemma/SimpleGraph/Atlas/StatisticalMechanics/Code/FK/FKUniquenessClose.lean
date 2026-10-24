import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKUniquenessClose
open MeasureTheory Set Filter Topology StatMech StatMech.FK


/--
[boxEdgeOpenEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma boxEdgeOpenEvent_isIncreasing_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  IsIncreasing (boxEdgeOpenEvent d N eb) := by
-- proof
  apply StatMech.FK.boxEdgeOpenEvent_isIncreasing d N eb

/--
[fkEdgeOpenEvent_edgeIncl_eq_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma fkEdgeOpenEvent_edgeIncl_eq_boxRestrict_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  fkEdgeOpenEvent (edgeIncl d N eb) = boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) := by
-- proof
  apply StatMech.FK.fkEdgeOpenEvent_edgeIncl_eq_boxRestrict d N eb

/--
[wiredEdgeDensity_q2_eq_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma wiredEdgeDensity_q2_eq_real_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.wiredEdgeDensity_q2_eq_real d N eb hp hp1

/--
[freeEdgeDensity_q2_eq_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma freeEdgeDensity_q2_eq_real_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.freeEdgeDensity_q2_eq_real d N eb hp hp1

/--
[wiredEdgeDensity_q2_eq_fkWiredLimitValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma wiredEdgeDensity_q2_eq_fkWiredLimitValue_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = fkWiredLimitValue N hp hp1 (boxEdgeOpenEvent d N eb) := by
-- proof
  apply StatMech.FK.wiredEdgeDensity_q2_eq_fkWiredLimitValue d N eb hp hp1

/--
[wiredEdgeDensity_q2_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma wiredEdgeDensity_q2_tendsto_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
-- proof
  apply StatMech.FK.wiredEdgeDensity_q2_tendsto d N eb hp hp1

/--
[isIncreasing_boxRestrict_boxEdgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma isIncreasing_boxRestrict_boxEdgeOpenEvent_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  IsIncreasing (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.isIncreasing_boxRestrict_boxEdgeOpenEvent d N eb

/--
[hcrit_edgeOpenEvent_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma hcrit_edgeOpenEvent_q2_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdens : freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.hcrit_edgeOpenEvent_q2 d N eb hp hp1 hdens

/--
[fk_uniqueness_off_countable_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessClose.lean)
-/
@[path]
private lemma fk_uniqueness_off_countable_q2_eq
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hb : Monotone (wiredEdgeDensity d 2 (edgeIncl d N eb)))
  (heq_at_cont : ∀ p, ContinuousAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) p → freeEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb) p) :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))), ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb))) → phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) ∧ phi.real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) := by
-- proof
  apply StatMech.FK.fk_uniqueness_off_countable_q2 d N eb hb heq_at_cont


-- created on 2026-10-23
