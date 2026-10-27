import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
open Finset Filter Topology StatMech StatMech.Ising


/--
[psv_adj_unique_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_adj_unique_coord_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (h : (∑ i, (x i - y i).natAbs) = 1) :
-- imply
  ∃ i : Fin d, (x i - y i).natAbs = 1 ∧ ∀ j, j ≠ i → x j = y j := by
-- proof
  apply StatMech.Ising.psv_adj_unique_coord h

/--
[psv_nbr_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_nbr_card_le_eq
  {d : ℕ}
  {x : Site d}
  {T : Finset (Site d)} :
-- imply
  (T.filter (fun y => (hypercubicLattice d).Adj x y)).card ≤ 2 * d := by
-- proof
  apply StatMech.Ising.psv_nbr_card_le x T

/--
[psv_volume_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_volume_card_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  (boxFinset d n).card = (2 * n + 1) ^ d := by
-- proof
  apply StatMech.Ising.psv_volume_card d n

/--
[psv_volume_card_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_volume_card_real_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  ((boxFinset d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
-- proof
  apply StatMech.Ising.psv_volume_card_real d n

/--
[psv_mem_Bdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_mem_Bdry_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d} :
-- imply
  x ∈ psv_Bdry d n ↔ x ∈ box d (n + 1) ∧ x ∉ box d n := by
-- proof
  apply StatMech.Ising.psv_mem_Bdry

/--
[psv_Bdry_card_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_Bdry_card_val_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  (psv_Bdry d n).card = (2 * (n + 1) + 1) ^ d - (2 * (n + 1) - 1) ^ d := by
-- proof
  apply StatMech.Ising.psv_Bdry_card_val d n

/--
[psv_Bdry_card_real_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_Bdry_card_real_le_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  ((psv_Bdry d n).card : ℝ) ≤ 2 * (d * (2 * (n : ℝ) + 3) ^ (d - 1)) := by
-- proof
  apply StatMech.Ising.psv_Bdry_card_real_le d n

/--
[psv_diff_char](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_diff_char_eq
  {d : ℕ}
  {n : ℕ}
  {p : Site d × Site d}
-- given
  (hp : p ∈ bondPairsTouch d n \ bondPairsInternal d n) :
-- imply
  (hypercubicLattice d).Adj p.1 p.2 ∧ ((p.1 ∈ box d n ∧ p.2 ∈ box d (n + 1) ∧ p.2 ∉ box d n) ∨ (p.2 ∈ box d n ∧ p.1 ∈ box d (n + 1) ∧ p.1 ∉ box d n)) := by
-- proof
  apply StatMech.Ising.psv_diff_char n hp

/--
[psv_ordered_diff_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_ordered_diff_le_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (bondPairsTouch d n \ bondPairsInternal d n).card ≤ (((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter (fun q => (hypercubicLattice d).Adj q.1 q.2)).card * 2 := by
-- proof
  apply StatMech.Ising.psv_ordered_diff_le n

/--
[psv_filt_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_filt_card_le_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (((psv_Bdry d n) ×ˢ (boxFinset d (n + 1))).filter (fun q => (hypercubicLattice d).Adj q.1 q.2)).card ≤ (psv_Bdry d n).card * (2 * d) := by
-- proof
  apply StatMech.Ising.psv_filt_card_le n

/--
[psv_numerator_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_numerator_card_le_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℕ) ≤ (psv_Bdry d n).card * (4 * d) := by
-- proof
  apply StatMech.Ising.psv_numerator_card_le n

/--
[psv_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_ratio_le_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ) / ((boxFinset d n).card : ℝ) ≤ (8 * (d : ℝ) ^ 2 * 3 ^ (d - 1)) / (2 * (n : ℝ) + 1) := by
-- proof
  apply StatMech.Ising.psv_ratio_le n hd

/--
[psv_ratio_card_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_ratio_card_tendsto_zero_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ) / ((boxFinset d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.psv_ratio_card_tendsto_zero d hd

/--
[psv_ratio_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_ratio_tendsto_zero_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => (|β| * ((bondFinsetTouch d n \ bondFinsetInternal d n).card : ℝ)) / ((boxFinset d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.psv_ratio_tendsto_zero d hd β

/--
[psv_plus_free_pressure_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_plus_free_pressure_indep_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (β h : ℝ) :
-- imply
  Tendsto (fun n => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h) / ((boxFinset d n).card : ℝ) - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) β h) / ((boxFinset d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.psv_plus_free_pressure_indep hd β h

/--
[psv_boxPressure_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_boxPressure_full_eq
  {d : ℕ}
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d)
  (β h : ℝ) :
-- imply
  ConvexOn ℝ Set.univ (fun β' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β' h)) ∧ ConvexOn ℝ Set.univ (fun h' : ℝ => Real.log (fvZ (plusField d) n (bondFinsetTouch d n) β h')) ∧ Tendsto (fun m => Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h) / ((boxFinset d m).card : ℝ) - Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h) / ((boxFinset d m).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.psv_boxPressure_full hd n β h

/--
[psv_boxPressure_plus_free_same_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean)
-/
@[path]
private lemma psv_boxPressure_plus_free_same_limit_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (β h p : ℝ)
  (hplus : Tendsto (fun m => Real.log (fvZ (plusField d) m (bondFinsetTouch d m) β h) / ((boxFinset d m).card : ℝ)) atTop (𝓝 p)) :
-- imply
  Tendsto (fun m => Real.log (fvZ (minusField d) m (bondFinsetInternal d m) β h) / ((boxFinset d m).card : ℝ)) atTop (𝓝 p) := by
-- proof
  apply StatMech.Ising.psv_boxPressure_plus_free_same_limit hd β h p hplus


-- created on 2026-10-23
