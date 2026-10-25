import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.ConvexGapHC.Part2
open Finset Real Set StatMech StatMech.Probability


/--
[cvg_convexGap_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_convexGap_le_eq
  [Fintype ι]
  [DecidableEq ι]
  {G : ℝ → ℝ}
  {u : ℝ}
-- given
  (hG : ConvexOn ℝ (Icc (0:ℝ) 1) G)
  (h0 : G 0 ≤ 0)
  (h1 : G 1 ≤ 0)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  G u ≤ 0 := by
-- proof
  apply StatMech.Probability.cvg_convexGap_le hG h0 h1 hu0 hu1

/--
[cvg_convexOn_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_convexOn_sum_eq
  [Fintype ι]
  [DecidableEq ι]
  {s : Finset α}
  {g : α → ℝ → ℝ}
  {D : Set ℝ}
-- given
  (hD : Convex ℝ D)
  (hg : ∀ a ∈ s, ConvexOn ℝ D (g a)) :
-- imply
  ConvexOn ℝ D (fun u => ∑ a ∈ s, g a u) := by
-- proof
  apply StatMech.Probability.cvg_convexOn_sum s g hD hg

/--
[cvg_oneSubPow_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_oneSubPow_convexOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {k : ℕ} :
-- imply
  ConvexOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => (1 - u) ^ k) := by
-- proof
  apply StatMech.Probability.cvg_oneSubPow_convexOn k

/--
[cvg_L_convexOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_L_convexOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool} :
-- imply
  ConvexOn ℝ (Icc (0:ℝ) 1) (fun u => ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
-- proof
  apply StatMech.Probability.cvg_L_convexOn p φ

/--
[cvg_Q_firstDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_Q_firstDeriv_eq
  [Fintype ι]
  [DecidableEq ι]
  {m u : ℝ}
-- given
  (hu : (2:ℝ) - u ≠ 0) :
-- imply
  HasDerivAt (fun y : ℝ => Real.exp (m * (y / (2 - y)))) (Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2))) u := by
-- proof
  apply StatMech.Probability.cvg_Q_firstDeriv m u hu

/--
[cvg_Q_secondDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_Q_secondDeriv_eq
  [Fintype ι]
  [DecidableEq ι]
  {m u : ℝ}
-- given
  (hu : (2:ℝ) - u ≠ 0) :
-- imply
  HasDerivAt (fun y : ℝ => Real.exp (m * (y / (2 - y))) * (m * (2 / (2 - y) ^ 2))) ((Real.exp (m * (u / (2 - u))) * (m * (2 / (2 - u) ^ 2))) * (m * (2 / (2 - u) ^ 2)) + Real.exp (m * (u / (2 - u))) * (m * (4 / (2 - u) ^ 3))) u := by
-- proof
  apply StatMech.Probability.cvg_Q_secondDeriv m u hu

/--
[cvg_Q_concaveOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_Q_concaveOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : ℝ}
-- given
  (hm0 : m ≤ 0)
  (hm1 : -1 ≤ m) :
-- imply
  ConcaveOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => Real.exp (m * (u / (2 - u)))) := by
-- proof
  apply StatMech.Probability.cvg_Q_concaveOn hm0 hm1

/--
[cvg_R_concaveOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_R_concaveOn_eq
  [Fintype ι]
  [DecidableEq ι]
  {δ T : ℝ}
-- given
  (hδlo : Real.exp (-1) ≤ δ)
  (hδhi : δ ≤ 1)
  (hT : 0 ≤ T) :
-- imply
  ConcaveOn ℝ (Icc (0:ℝ) 1) (fun u : ℝ => δ ^ (u / (2 - u)) * T) := by
-- proof
  apply StatMech.Probability.cvg_R_concaveOn hδlo hδhi hT

/--
[cvg_openResidue_of_concaveR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_openResidue_of_concaveR_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hconc : ConcaveOn ℝ (Icc (0:ℝ) 1) (fun u => (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.cvg_openResidue_of_concaveR hp0 hp1 φ hconc hu0 hu1

/--
[cvg_maxInfl_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_maxInfl_le_one_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ 1 := by
-- proof
  apply StatMech.Probability.cvg_maxInfl_le_one hp0 hp1 φ

/--
[cvg_openResidue_largeDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_openResidue_largeDelta_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hδlo : Real.exp (-1) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
  (hu0 : 0 < u)
  (hu1 : u < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.cvg_openResidue_largeDelta hp0 hp1 φ hδlo hu0 hu1

/--
[cvg_openResidue_of_smallDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_openResidue_of_smallDelta_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : cvg_smallDeltaResidue q} :
-- imply
  frh_openResidue q := by
-- proof
  apply StatMech.Probability.cvg_openResidue_of_smallDelta H

/--
[cvg_martingaleHC_of_smallDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean)
-/
@[path]
private lemma cvg_martingaleHC_of_smallDelta_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : cvg_smallDeltaResidue q} :
-- imply
  mxd_martingaleHC_statement q := by
-- proof
  apply StatMech.Probability.cvg_martingaleHC_of_smallDelta H


-- created on 2026-10-23
