import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.PercoItems
open MeasureTheory Set Filter Topology StatMech StatMech.Sharpness


/--
[perco_ode_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma perco_ode_antitone_eq
  {d : ℕ}
  {p₀ : ℝ}
  {f : ℝ → ℝ}
-- given
  (hp₀ : 0 < p₀)
  (hdiff : ∀ p ∈ Ico p₀ 1, DifferentiableAt ℝ f p)
  (hineq : ∀ p ∈ Ioo p₀ 1, (1 / (p * (1 - p))) * (1 - f p) ≤ deriv f p) :
-- imply
  AntitoneOn (fun p => (1 - f p) * (p / (1 - p))) (Ico p₀ 1) := by
-- proof
  apply StatMech.Sharpness.perco_ode_antitone p₀ hp₀ f hdiff hineq

/--
[profile_ge_of_diffineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma profile_ge_of_diffineq_eq
  {d : ℕ}
  {p₀ : ℝ}
  {f : ℝ → ℝ}
  {p : ℝ}
-- given
  (hp₀ : 0 < p₀)
  (hp₀1 : p₀ < 1)
  (hdiff : ∀ p ∈ Ico p₀ 1, DifferentiableAt ℝ f p)
  (hineq : ∀ p ∈ Ioo p₀ 1, (1 / (p * (1 - p))) * (1 - f p) ≤ deriv f p)
  (hf0 : 0 ≤ f p₀)
  (hpp₀ : p₀ ≤ p)
  (hp1 : p < 1) :
-- imply
  (p - p₀) / (p * (1 - p₀)) ≤ f p := by
-- proof
  apply StatMech.Sharpness.profile_ge_of_diffineq p₀ hp₀ hp₀1 f hdiff hineq hf0 hpp₀ hp1

/--
[percolationEvent_subset_crossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma percolationEvent_subset_crossingEvent_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  percolationEvent d ⊆ crossingEvent d n := by
-- proof
  apply StatMech.Sharpness.percolationEvent_subset_crossingEvent n

/--
[theta_le_crossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma theta_le_crossProb_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  theta d p hp ≤ crossProb d p hp n := by
-- proof
  apply StatMech.Sharpness.theta_le_crossProb p hp n

/--
[item1_meanfield_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma item1_meanfield_lower_bound_eq
  {d : ℕ}
  {p₀ : ℝ}
  {f : ℕ → ℝ → ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hp₀ : 0 < p₀)
  (hp₀1 : p₀ < 1)
  (hfval : ∀ n, f n (p : ℝ) = crossProb d p hp n)
  (hdiff : ∀ n, ∀ q ∈ Ico p₀ 1, DifferentiableAt ℝ (f n) q)
  (hineq : ∀ n, ∀ q ∈ Ioo p₀ 1, (1 / (q * (1 - q))) * (1 - f n q) ≤ deriv (f n) q)
  (hf0 : ∀ n, 0 ≤ f n p₀)
  (hpp₀ : p₀ ≤ (p : ℝ))
  (hp1 : (p : ℝ) < 1)
  (htends : Tendsto (fun n => crossProb d p hp n) atTop (𝓝 (theta d p hp))) :
-- imply
  ((p : ℝ) - p₀) / ((p : ℝ) * (1 - p₀)) ≤ theta d p hp := by
-- proof
  apply StatMech.Sharpness.item1_meanfield_lower_bound p hp p₀ hp₀ hp₀1 f hfval hdiff hineq hf0 hpp₀ hp1 htends

/--
[susceptibility_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma susceptibility_finite_eq
  {d : ℕ}
  {chi Sval phival : ℝ}
-- given
  (hchi : 0 ≤ chi)
  (hphi1 : phival < 1)
  (hself : chi ≤ Sval + phival * chi) :
-- imply
  0 ≤ chi ∧ chi ≤ Sval / (1 - phival) := by
-- proof
  apply StatMech.Sharpness.susceptibility_finite chi Sval phival hchi hphi1 hself

/--
[subcritical_exp_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma subcritical_exp_decay_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hS0 : origin d ∈ S)
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hstep : ∀ k, crossProb d p hp ((k + 1) * L) ≤ phi d p hp S * crossProb d p hp (k * L)) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.subcritical_exp_decay p hp S hS0 hphi L hL hstep

/--
[pc_le_tildePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma pc_le_tildePc_eq
  {d : ℕ}
-- given
  (hpos : ∀ t : ℝ≥0, tildePc d < t → ∀ ht : t ≤ 1, 0 < theta d t ht) :
-- imply
  pc d ≤ tildePc d := by
-- proof
  apply StatMech.Sharpness.pc_le_tildePc hpos

/--
[tildePc_le_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma tildePc_le_pc_eq
  {d : ℕ}
-- given
  (hzero : ∀ t ∈ tildePcSet d, ∀ ht : t ≤ 1, theta d t ht = 0) :
-- imply
  tildePc d ≤ pc d := by
-- proof
  apply StatMech.Sharpness.tildePc_le_pc hzero

/--
[bc_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoItems.lean)
-/
@[path]
private lemma bc_eq_eq
  {d : ℕ}
-- given
  (hpos : ∀ t : ℝ≥0, tildePc d < t → ∀ ht : t ≤ 1, 0 < theta d t ht)
  (hzero : ∀ t ∈ tildePcSet d, ∀ ht : t ≤ 1, theta d t ht = 0) :
-- imply
  pc d = tildePc d := by
-- proof
  apply StatMech.Sharpness.bc_eq hpos hzero


-- created on 2026-10-23
