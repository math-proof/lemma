import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[boxBdryConnEvent_eq_iUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma boxBdryConnEvent_eq_iUnion_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  boxBdryConnEvent d n = ⋃ v ∈ {v : boxVerts d n | boxBoundary d n v}, boxConnEvent d n (IsingFK.boxOrigin d n) v := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_eq_iUnion d n

/--
[isClopen_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma isClopen_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  IsClopen (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.isClopen_boxBdryConnEvent d n

/--
[measurableSet_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma measurableSet_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  MeasurableSet (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.measurableSet_boxBdryConnEvent d n

/--
[isIncreasing_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma isIncreasing_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  IsIncreasing (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.isIncreasing_boxBdryConnEvent d n

/--
[extendEdge_preimage_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma extendEdge_preimage_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  extendEdge d n ⁻¹' (boxBdryConnEvent d n) = {ω : ConfigSpace (Sym2 (boxVerts d n)) | ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
-- proof
  apply StatMech.FK.extendEdge_preimage_boxBdryConnEvent d n

/--
[wiredFiniteMeasure_real_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) = wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_boxBdryConnEvent d n hp hp1

/--
[boxBoundaryConnProfile_eq_wiredFiniteMeasure_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma boxBoundaryConnProfile_eq_wiredFiniteMeasure_real_eq
  {d : ℕ}
  {d n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n = (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.boxBoundaryConnProfile_eq_wiredFiniteMeasure_real d n hp hp1

/--
[boxBoundaryConnProfile_tendsto_of_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxTailLimit.lean)
-/
@[path]
private lemma boxBoundaryConnProfile_tendsto_of_diag_eq
  {d : ℕ}
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdiag : Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)) atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2)))) :
-- imply
  Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n) atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) := by
-- proof
  apply StatMech.FK.boxBoundaryConnProfile_tendsto_of_diag d hp hp1 hdiag


-- created on 2026-10-23
