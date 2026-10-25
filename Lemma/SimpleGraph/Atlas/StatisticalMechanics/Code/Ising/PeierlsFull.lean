import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[peierlsRatio_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsRatio_def_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  peierlsRatio d β = (2 * d : ℝ) * Real.exp (-(2 * β)) := by
-- proof
  apply StatMech.Ising.peierlsRatio_def d β

/--
[peierlsRatio_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsRatio_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  0 ≤ peierlsRatio d β := by
-- proof
  apply StatMech.Ising.peierlsRatio_nonneg d β

/--
[peierlsSummand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsSummand_eq_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {ℓ : ℕ} :
-- imply
  (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ) = (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ := by
-- proof
  apply StatMech.Ising.peierlsSummand_eq d β ℓ

/--
[peierlsBound_eq_closedForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsBound_eq_closedForm_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
-- given
  (hx : ‖peierlsRatio d β‖ < 1) :
-- imply
  peierlsBound d β = (peierlsRatio d β) / (1 - peierlsRatio d β) ^ 2 := by
-- proof
  apply StatMech.Ising.peierlsBound_eq_closedForm d β hx

/--
[peierlsRatio_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsRatio_tendsto_atTop_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Tendsto (fun β : ℝ => peierlsRatio d β) atTop (nhds 0) := by
-- proof
  apply StatMech.Ising.peierlsRatio_tendsto_atTop d

/--
[closedForm_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma closedForm_tendsto_zero_eq
  {d : ℕ} :
-- imply
  Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
-- proof
  apply StatMech.Ising.closedForm_tendsto_zero

/--
[peierlsBound_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsBound_tendsto_atTop_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Tendsto (fun β : ℝ => peierlsBound d β) atTop (nhds 0) := by
-- proof
  apply StatMech.Ising.peierlsBound_tendsto_atTop d

/--
[exists_beta_peierlsBound_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma exists_beta_peierlsBound_lt_half_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → peierlsBound d β < 1 / 2 := by
-- proof
  apply StatMech.Ising.exists_beta_peierlsBound_lt_half d

/--
[peierlsBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierlsBound_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  0 ≤ peierlsBound d β := by
-- proof
  apply StatMech.Ising.peierlsBound_nonneg d β

/--
[contour_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma contour_card_le_eq
  {d : ℕ}
  {d : ℕ}
  {B : Finset (Site d)}
  {ℓ : ℕ}
-- given
  (hB : B.card ≤ ℓ) :
-- imply
  ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ) ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by
-- proof
  apply StatMech.Ising.contour_card_le d B ℓ hB

/--
[contour_card_le_peierlsSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma contour_card_le_peierlsSummand_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {B : Finset (Site d)}
  {ℓ : ℕ}
-- given
  (hB : B.card ≤ ℓ) :
-- imply
  ((B.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card : ℝ) * Real.exp (-(2 * β) * ℓ) ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * ℓ) := by
-- proof
  apply StatMech.Ising.contour_card_le_peierlsSummand d β B ℓ hB

/--
[probOriginMinus_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma probOriginMinus_nonneg_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  0 ≤ probOriginMinus η n B β h := by
-- proof
  apply StatMech.Ising.probOriginMinus_nonneg η n B β h

/--
[fvMagOrigin_eq_one_sub_two_mul_probOriginMinus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma fvMagOrigin_eq_one_sub_two_mul_probOriginMinus_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  fvMagOrigin η n B β h = 1 - 2 * probOriginMinus η n B β h := by
-- proof
  apply StatMech.Ising.fvMagOrigin_eq_one_sub_two_mul_probOriginMinus η n B β h

/--
[fvMagOrigin_pos_of_probOriginMinus_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma fvMagOrigin_pos_of_probOriginMinus_lt_half_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (hP : probOriginMinus η n B β h < 1 / 2) :
-- imply
  0 < fvMagOrigin η n B β h := by
-- proof
  apply StatMech.Ising.fvMagOrigin_pos_of_probOriginMinus_lt_half η n B β h hP

/--
[peierls_long_range_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierls_long_range_order_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → PeierlsContourBound d n β → plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order hd

/--
[peierls_long_range_order'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean)
-/
@[path]
private lemma peierls_long_range_order'_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hGeom : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → PeierlsContourBound d n β) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order' hd hGeom


-- created on 2026-10-23
