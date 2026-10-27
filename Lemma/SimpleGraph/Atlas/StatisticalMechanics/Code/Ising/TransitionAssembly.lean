import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
open Real StatMech StatMech.Ising


/--
[ita_hmag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_hmag_nonneg_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ magnetization d β := by
-- proof
  apply StatMech.Ising.ita_hmag_nonneg d hβ

/--
[ita_hFKsub_of_atCriticality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_hFKsub_of_atCriticality_eq
  {d : ℕ}
-- given
  (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1), FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
-- imply
  ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 → FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
-- proof
  apply StatMech.Ising.ita_hFKsub_of_atCriticality d hθpc

/--
[ita_ising_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_ising_transition_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1), FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.Ising.ita_ising_transition d hd hisingBox hθpc hpc1

/--
[ita_ising_transition_two_of_fkNonPercolationBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_ising_transition_two_of_fkNonPercolationBound_eq
-- given
  (hθpc : ∀ (hp : 0 < FK.fkPc 2 2) (hp1 : FK.fkPc 2 2 < 1), FK.fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hBound : ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p → FK.FkNonPercolationBound 2 hp hp1 (by norm_num : (0 : ℝ) < 2)) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization 2 β = 0) ∧ (∀ β, βc < β → 0 < magnetization 2 β) := by
-- proof
  apply StatMech.Ising.ita_ising_transition_two_of_fkNonPercolationBound hθpc hBound

/--
[ita_peierls_phase_separation_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_peierls_phase_separation_two_eq :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.ita_peierls_phase_separation_two

/--
[ita_isingBetaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_isingBetaC_eq_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1), FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.Ising.ita_isingBetaC_eq d hd hisingBox hθpc hpc1

/--
[ita_isingBetaC_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionAssembly.lean)
-/
@[path]
private lemma ita_isingBetaC_pos_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2) (pOfBeta β) (boxOrigin d (n + 1)))
  (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1), FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.Ising.ita_isingBetaC_pos d hd hisingBox hθpc hpc1


-- created on 2026-10-23
