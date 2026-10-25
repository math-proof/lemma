import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
open MeasureTheory Finset StatMech StatMech.Sharpness


/--
[bondParam_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma bondParam_le_one_eq
  {d : ℕ}
  {β : ℝ} :
-- imply
  bondParam β ≤ 1 := by
-- proof
  apply StatMech.Sharpness.bondParam_le_one β

/--
[phiBeta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma phiBeta_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)} :
-- imply
  0 ≤ phiBeta d β S := by
-- proof
  apply StatMech.Sharpness.phiBeta_nonneg d β S

/--
[mem_tildeBetaCPercoSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma mem_tildeBetaCPercoSet_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  β ∈ tildeBetaCPercoSet d ↔ 0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d β S < 1 := by
-- proof
  apply StatMech.Sharpness.mem_tildeBetaCPercoSet

/--
[freeCorr_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma freeCorr_self_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)}
-- given
  (a : {v // v ∈ S}) :
-- imply
  freeCorr d β S a a = 1 := by
-- proof
  apply StatMech.Sharpness.freeCorr_self d β S a

/--
[abs_freeCorr_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma abs_freeCorr_le_one_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)}
-- given
  (a b : {v // v ∈ S}) :
-- imply
  |freeCorr d β S a b| ≤ 1 := by
-- proof
  apply StatMech.Sharpness.abs_freeCorr_le_one d β S a b

/--
[freeCorr_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma freeCorr_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)}
-- given
  (hβ : 0 ≤ β)
  (a b : {v // v ∈ S}) :
-- imply
  0 ≤ freeCorr d β S a b := by
-- proof
  apply StatMech.Sharpness.freeCorr_nonneg d hβ S a b

/--
[corrOriginInner_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma corrOriginInner_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ corrOriginInner d β S x := by
-- proof
  apply StatMech.Sharpness.corrOriginInner_nonneg d hβ S x

/--
[phiIsing_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma phiIsing_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {S : Finset (Site d)}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ phiIsing d β S := by
-- proof
  apply StatMech.Sharpness.phiIsing_nonneg d hβ S

/--
[mem_tildeBetaCIsingSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean)
-/
@[path]
private lemma mem_tildeBetaCIsingSet_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  β ∈ tildeBetaCIsingSet d ↔ 0 ≤ β ∧ ∃ S : Finset (Site d), origin d ∈ S ∧ phiIsing d β S < 1 := by
-- proof
  apply StatMech.Sharpness.mem_tildeBetaCIsingSet


-- created on 2026-10-23
