import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Percolation


/--
[pcRatio_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcRatio_def_eq
  {d : ℕ}
  {p : ℝ} :
-- imply
  pcRatio p = 4 * (1 - p) := by
-- proof
  apply StatMech.Percolation.pcRatio_def p

/--
[pcSummand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcSummand_eq_eq
  {d : ℕ}
  {p : ℝ}
  {ℓ : ℕ} :
-- imply
  (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (pcRatio p) ^ ℓ := by
-- proof
  apply StatMech.Percolation.pcSummand_eq p ℓ

/--
[pcUpperBound_eq_closedForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcUpperBound_eq_closedForm_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hx : ‖pcRatio p‖ < 1) :
-- imply
  pcUpperBound p = (pcRatio p) / (1 - pcRatio p) ^ 2 := by
-- proof
  apply StatMech.Percolation.pcUpperBound_eq_closedForm p hx

/--
[pcRatio_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcRatio_tendsto_one_eq
  {d : ℕ} :
-- imply
  Tendsto (fun p : ℝ => pcRatio p) (nhds 1) (nhds 0) := by
-- proof
  apply StatMech.Percolation.pcRatio_tendsto_one

/--
[pcClosedForm_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcClosedForm_tendsto_zero_eq
  {d : ℕ} :
-- imply
  Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
-- proof
  apply StatMech.Percolation.pcClosedForm_tendsto_zero

/--
[pcUpperBound_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcUpperBound_tendsto_one_eq
  {d : ℕ} :
-- imply
  Tendsto (fun p : ℝ => pcUpperBound p) (nhds 1) (nhds 0) := by
-- proof
  apply StatMech.Percolation.pcUpperBound_tendsto_one

/--
[exists_p_lt_one_pcUpperBound_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma exists_p_lt_one_pcUpperBound_lt_one_eq
  {d : ℕ} :
-- imply
  ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → pcUpperBound p < 1 := by
-- proof
  apply StatMech.Percolation.exists_p_lt_one_pcUpperBound_lt_one

/--
[pcUpperBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcUpperBound_nonneg_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : p ≤ 1) :
-- imply
  0 ≤ pcUpperBound p := by
-- proof
  apply StatMech.Percolation.pcUpperBound_nonneg hp

/--
[pcContour_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcContour_card_le_eq
  {d : ℕ}
  {B : Finset (Site 2)}
  {ℓ : ℕ}
-- given
  (hB : B.card ≤ ℓ) :
-- imply
  ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ) ≤ (ℓ : ℝ) * (4 : ℝ) ^ ℓ := by
-- proof
  apply StatMech.Percolation.pcContour_card_le B ℓ hB

/--
[pcContour_card_le_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pcContour_card_le_summand_eq
  {d : ℕ}
  {p : ℝ}
  {B : Finset (Site 2)}
  {ℓ : ℕ}
-- given
  (hp : p ≤ 1)
  (hB : B.card ≤ ℓ) :
-- imply
  ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ) * (1 - p) ^ ℓ ≤ (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ := by
-- proof
  apply StatMech.Percolation.pcContour_card_le_summand hp B ℓ hB

/--
[theta_pos_of_contourBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma theta_pos_of_contourBound_eq
  {d : ℕ}
  {p : NNReal}
-- given
  (hp : p ≤ 1)
  (hContour : PcContourBound p hp)
  (hBound : pcUpperBound (p : ℝ) < 1) :
-- imply
  0 < theta 2 p hp := by
-- proof
  apply StatMech.Percolation.theta_pos_of_contourBound hp hContour hBound

/--
[not_mem_subcriticalSet_of_theta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma not_mem_subcriticalSet_of_theta_pos_eq
  {d : ℕ}
  {p : NNReal}
-- given
  (hp : p ≤ 1)
  (hθ : 0 < theta 2 p hp) :
-- imply
  p ∉ subcriticalSet 2 := by
-- proof
  apply StatMech.Percolation.not_mem_subcriticalSet_of_theta_pos hp hθ

/--
[pc_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pc_lt_one_eq
  {d : ℕ}
-- given
  (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ (p : NNReal) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
-- imply
  pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_lt_one hGeom

/--
[pc_pos_and_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean)
-/
@[path]
private lemma pc_pos_and_lt_one_eq
  {d : ℕ}
-- given
  (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ (p : NNReal) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
-- imply
  0 < pc 2 ∧ pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_pos_and_lt_one hGeom


-- created on 2026-10-23
