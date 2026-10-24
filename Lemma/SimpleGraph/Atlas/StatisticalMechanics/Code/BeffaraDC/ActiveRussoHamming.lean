import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.ActiveRussoHamming
open StatMech StatMech.BeffaraDC


/--
[active_fkg_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma active_fkg_cov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  activeMean G (fun _ => p) q f * activeMean G (fun _ => p) q g ≤ activeMean G (fun _ => p) q (fun ω => f ω * g ω) := by
-- proof
  apply StatMech.BeffaraDC.active_fkg_cov G hp hp1 hq hf hg

/--
[activeMean_indicator_hamming_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma activeMean_indicator_hamming_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)} :
-- imply
  activeMean G (fun _ => p) q (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ)) = 0 := by
-- proof
  apply StatMech.BeffaraDC.activeMean_indicator_hamming_zero G p q A

/--
[activeCov_numOpen_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma activeCov_numOpen_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeCov G (fun _ => p) q f (fun ω => (numOpen ω : ℝ)) = ∑ e : G.edgeSet, activeCov G (fun _ => p) q f (OSSS.Lindeberg.coord e) := by
-- proof
  apply StatMech.BeffaraDC.activeCov_numOpen_eq_sum G p q f

/--
[active_prob_mul_mean_hamming_le_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma active_prob_mul_mean_hamming_le_cov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeProbOf G (fun _ => p) q A * activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ)) ≤ activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ)) (fun ω => (numOpen ω : ℝ)) := by
-- proof
  apply StatMech.BeffaraDC.active_prob_mul_mean_hamming_le_cov G hp hp1 hq A hA

/--
[active_russoHamming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma active_russoHamming_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  4 * activeProbOf G (fun _ => p) q A * activeMean G (fun _ => p) q (fun ω => (hammingToSet A ω : ℝ)) ≤ deriv (fun x => activeProbOf G (fun _ => x) q A) p := by
-- proof
  apply StatMech.BeffaraDC.active_russoHamming G hp hp1 hq A hA

/--
[active_fkg_anticorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma active_fkg_anticorr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Antitone f)
  (hg : Monotone g) :
-- imply
  activeMean G (fun _ => p) q (fun ω => f ω * g ω) ≤ activeMean G (fun _ => p) q f * activeMean G (fun _ => p) q g := by
-- proof
  apply StatMech.BeffaraDC.active_fkg_anticorr G hp hp1 hq hf hg

/--
[activeMean_antitoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma activeMean_antitoneOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p₁ p₂ q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp₂ : p₂ < 1)
  (hq : 1 ≤ q)
  (hf : Antitone f) :
-- imply
  AntitoneOn (fun p => activeMean G (fun _ => p) q f) (Set.Icc p₁ p₂) := by
-- proof
  apply StatMech.BeffaraDC.activeMean_antitoneOn G hp₁ hp₂ hq hf

/--
[active_gronwall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma active_gronwall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
  {c : ℝ}
  {p₁ p₂ : ℝ}
-- given
  (hp₁ : 0 < p₁)
  (hp₂ : p₂ < 1)
  (hq : 0 < q)
  (hp : p₁ ≤ p₂)
  (hdiff : ∀ p ∈ Set.Icc p₁ p₂, c * activeProbOf G (fun _ => p) q A ≤ deriv (fun x => activeProbOf G (fun _ => x) q A) p) :
-- imply
  activeProbOf G (fun _ => p₁) q A ≤ activeProbOf G (fun _ => p₂) q A * Real.exp (-c * (p₂ - p₁)) := by
-- proof
  apply StatMech.BeffaraDC.active_gronwall G q A c hp₁ hp₂ hq hp hdiff

/--
[active_russoHammingIntegrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveRussoHamming.lean)
-/
@[path]
private lemma active_russoHammingIntegrated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p₁ p₂ q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp₁ : 0 < p₁)
  (hp₁₂ : p₁ < p₂)
  (hp₂ : p₂ < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeProbOf G (fun _ => p₁) q A ≤ activeProbOf G (fun _ => p₂) q A * Real.exp (-4 * (p₂ - p₁) * activeMean G (fun _ => p₂) q (fun ω => (hammingToSet A ω : ℝ))) := by
-- proof
  apply StatMech.BeffaraDC.active_russoHammingIntegrated G hp₁ hp₁₂ hp₂ hq A hA


-- created on 2026-10-23
