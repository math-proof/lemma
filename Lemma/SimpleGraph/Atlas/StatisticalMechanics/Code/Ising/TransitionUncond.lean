import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.TransitionUncond
open Real StatMech StatMech.Ising


/--
[fkPc_two_pos_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionUncond.lean)
-/
@[path]
private lemma fkPc_two_pos_of_two_le_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d) :
-- imply
  0 < FK.fkPc d 2 := by
-- proof
  apply StatMech.Ising.fkPc_two_pos_of_two_le hd

/--
[ising_transition_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionUncond.lean)
-/
@[path]
private lemma ising_transition_uncond_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (htransition : ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.Ising.ising_transition_uncond d hd hmag_nonneg htransition hpc1

/--
[isingBetaC_eq_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionUncond.lean)
-/
@[path]
private lemma isingBetaC_eq_uncond_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (htransition : ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.Ising.isingBetaC_eq_uncond d hd hmag_nonneg htransition hpc1

/--
[isingBetaC_pos_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TransitionUncond.lean)
-/
@[path]
private lemma isingBetaC_pos_uncond_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (htransition : ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.Ising.isingBetaC_pos_uncond d hd hmag_nonneg htransition hpc1


-- created on 2026-10-23
