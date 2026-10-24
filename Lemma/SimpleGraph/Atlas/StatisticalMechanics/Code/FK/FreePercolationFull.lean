import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FreePercolationFull
open MeasureTheory StatMech StatMech.FK


/--
[frp_fkSubcriticalSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean)
-/
@[path]
private lemma frp_fkSubcriticalSet_bddAbove_eq
  {d : ℕ}
  {q : ℝ} :
-- imply
  BddAbove (fkSubcriticalSet d q) := by
-- proof
  apply StatMech.FK.frp_fkSubcriticalSet_bddAbove d q

/--
[frp_fkTheta_pos_of_gt_fkPc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean)
-/
@[path]
private lemma frp_fkTheta_pos_of_gt_fkPc_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hpc : fkPc d q < p) :
-- imply
  0 < fkTheta d hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 hq hpc

/--
[frp_measurableSet_percolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean)
-/
@[path]
private lemma frp_measurableSet_percolationEvent_eq
  {d : ℕ} :
-- imply
  MeasurableSet (Percolation.percolationEvent d) := by
-- proof
  apply StatMech.FK.frp_measurableSet_percolationEvent d

/--
[frp_isIncreasing_percolationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean)
-/
@[path]
private lemma frp_isIncreasing_percolationEvent_eq
  {d : ℕ} :
-- imply
  IsIncreasing (Percolation.percolationEvent d) := by
-- proof
  apply StatMech.FK.frp_isIncreasing_percolationEvent d

/--
[frp_free_percolation_above_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean)
-/
@[path]
private lemma frp_free_percolation_above_pc_eq
  {d : ℕ}
  {p p' q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hp' : 0 < p')
  (hp1' : p' < 1)
  (hpc' : fkPc d q < p')
  (hmono : (freeInfiniteVolume d hp' hp1' hq : Measure (ConfigSpace (Sym2 (Site d)))) ≼ (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
  (huniq : fkThetaFree d hp' hp1' hq (q := q) = fkTheta d hp' hp1' hq (q := q)) :
-- imply
  0 < fkThetaFree d hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.frp_free_percolation_above_pc d hp hp1 hq hp' hp1' hpc' hmono huniq

/--
[frp_free_percolation_above_pc_of_countable_agreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePercolationFull.lean)
-/
@[path]
private lemma frp_free_percolation_above_pc_of_countable_agreement_eq
  {d : ℕ}
  {p q : ℝ}
  {bad : Set ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hpc : fkPc d q < p)
  (hbad : bad.Countable)
  (hmono : ∀ {p' : ℝ} (hp' : 0 < p') (hp1' : p' < 1), fkPc d q < p' → (freeInfiniteVolume d hp' hp1' hq : Measure (ConfigSpace (Sym2 (Site d)))) ≼ (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
  (hagree : ∀ {p' : ℝ} (hp' : 0 < p') (hp1' : p' < 1), fkPc d q < p' → p' ∉ bad → fkThetaFree d hp' hp1' hq (q := q) = fkTheta d hp' hp1' hq (q := q)) :
-- imply
  0 < fkThetaFree d hp hp1 hq (q := q) := by
-- proof
  apply StatMech.FK.frp_free_percolation_above_pc_of_countable_agreement d hp hp1 hq hpc bad hbad hmono hagree


-- created on 2026-10-23
