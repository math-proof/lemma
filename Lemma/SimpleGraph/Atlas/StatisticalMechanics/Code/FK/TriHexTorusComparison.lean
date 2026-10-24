import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexTorusComparison
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexTorus_topologicalCorrection_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_topologicalCorrection_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (TorusSite L))}
  {q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  1 ≤ q ^ triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) ∧ q ^ triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega) ≤ q ^ 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_topologicalCorrection_bounds L omega hq

/--
[triHexTorus_topologicalCorrection_log_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_topologicalCorrection_log_bound_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (Sym2 (TorusSite L))}
  {q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  |Real.log (q ^ triHexTorusDefect L (FK.openSub (triangularTorusGraph L) omega))| ≤ 2 * Real.log q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_topologicalCorrection_log_bound L omega hq

/--
[triHexTorus_topologicalCorrection_logDensity_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_topologicalCorrection_logDensity_tendsto_zero_eq
  {q : ℝ}
-- given
  (hq : 1 ≤ q)
  (omega : ∀ L : ℕ, ConfigSpace (Sym2 (TorusSite L))) :
-- imply
  Filter.Tendsto (triHexTorusTopologicalCorrectionLogDensity q omega) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_topologicalCorrection_logDensity_tendsto_zero q hq omega

/--
[triHexTorusDualPartitionSum_eq_sectorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorusDualPartitionSum_eq_sectorSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pDual q : ℝ} :
-- imply
  triHexTorusDualPartitionSum L pDual q = triHexTorusDualSectorSum L 0 pDual q (fun _ => 1) + triHexTorusDualSectorSum L 1 pDual q (fun _ => 1) + triHexTorusDualSectorSum L 2 pDual q (fun _ => 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDualPartitionSum_eq_sectorSum L pDual q

/--
[triHexTorusDefectWeightedDualPartitionSum_eq_sectorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorusDefectWeightedDualPartitionSum_eq_sectorSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pDual q : ℝ} :
-- imply
  triHexTorusDefectWeightedDualPartitionSum L pDual q = triHexTorusDualSectorSum L 0 pDual q (fun _ => 1) + q * triHexTorusDualSectorSum L 1 pDual q (fun _ => 1) + q ^ 2 * triHexTorusDualSectorSum L 2 pDual q (fun _ => 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusDefectWeightedDualPartitionSum_eq_sectorSum L pDual q

/--
[triHexTorus_partition_duality_defectWeighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_partition_duality_defectWeighted_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  triHexTorusPrimalPartitionSum L p q * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ (triangularTorusGraph L).edgeFinset.card * q ^ Nat.card (TorusSite L) * triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_partition_duality_defectWeighted L hp hp1 hq

/--
[triHexTorus_numerator_duality_defectWeighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_numerator_duality_defectWeighted_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  triHexTorusPrimalNumerator L p q F * q ^ ((triangularTorusGraph L).edgeFinset.card + 1) = (p / (1 - BeffaraDC.dualParam p q)) ^ (triangularTorusGraph L).edgeFinset.card * q ^ Nat.card (TorusSite L) * triHexTorusDefectWeightedDualNumerator L (BeffaraDC.dualParam p q) q F := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_numerator_duality_defectWeighted L F hp hp1 hq

/--
[triHexTorus_defectWeighted_partition_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_defectWeighted_partition_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q ≤ triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q ∧ triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q ≤ q ^ 2 * triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_defectWeighted_partition_bounds L hp hp1 hq

/--
[triHexTorus_defectWeighted_numerator_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_defectWeighted_numerator_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ}
  {p q : ℝ}
-- given
  (hF : ∀ eta, 0 ≤ F eta)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F ≤ triHexTorusDefectWeightedDualNumerator L (BeffaraDC.dualParam p q) q F ∧ triHexTorusDefectWeightedDualNumerator L (BeffaraDC.dualParam p q) q F ≤ q ^ 2 * triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_defectWeighted_numerator_bounds L F hF hp hp1 hq

/--
[triHexTorus_defectWeighted_normalized_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusComparison.lean)
-/
@[path]
private lemma triHexTorus_defectWeighted_normalized_bounds_eq
  {L : ℕ}
  [Fact (2 < L)]
  {F : ConfigSpace (Sym2 (HexTorusVertex L)) → ℝ}
  {p q : ℝ}
-- given
  (hF : ∀ eta, 0 ≤ F eta)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hpart : 0 < triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) :
-- imply
  triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F / (q ^ 2 * triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) ≤ triHexTorusDefectWeightedDualNumerator L (BeffaraDC.dualParam p q) q F / triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q ∧ triHexTorusDefectWeightedDualNumerator L (BeffaraDC.dualParam p q) q F / triHexTorusDefectWeightedDualPartitionSum L (BeffaraDC.dualParam p q) q ≤ q ^ 2 * triHexTorusDualNumerator L (BeffaraDC.dualParam p q) q F / triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorus_defectWeighted_normalized_bounds L F hF hp hp1 hq hpart


-- created on 2026-10-23
