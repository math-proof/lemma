import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.Transition
open Real StatMech StatMech.Ising


/--
[pToBeta_two_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Transition.lean)
-/
@[path]
private lemma pToBeta_two_pos_eq
  {pc : ℝ}
-- given
  (hpc0 : 0 < pc)
  (hpc1 : pc < 1) :
-- imply
  0 < pToBeta 2 pc := by
-- proof
  apply StatMech.Ising.pToBeta_two_pos hpc0 hpc1

/--
[abstract_ising_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Transition.lean)
-/
@[path]
private lemma abstract_ising_transition_eq
  {mStar : ℝ → ℝ}
  {pc : ℝ}
-- given
  (hmag_nonneg : ∀ β, 0 ≤ mStar β)
  (htransition : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta 2 pc < β))
  (hpc0 : 0 < pc)
  (hpc1 : pc < 1) :
-- imply
  0 < pToBeta 2 pc ∧ (∀ β, 0 < β → β < pToBeta 2 pc → mStar β = 0) ∧ (∀ β, pToBeta 2 pc < β → 0 < mStar β) := by
-- proof
  apply StatMech.Ising.abstract_ising_transition mStar pc hmag_nonneg htransition hpc0 hpc1

/--
[ising_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Transition.lean)
-/
@[path]
private lemma ising_transition_eq
  {d : ℕ}
-- given
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (htransition : ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  ∃ βc : ℝ, 0 < βc ∧ (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧ (∀ β, βc < β → 0 < magnetization d β) := by
-- proof
  apply StatMech.Ising.ising_transition d hmag_nonneg htransition hpc0 hpc1

/--
[ising_betaC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Transition.lean)
-/
@[path]
private lemma ising_betaC_eq_eq
  {d : ℕ}
-- given
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (htransition : ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
-- proof
  apply StatMech.Ising.ising_betaC_eq d hmag_nonneg htransition hpc0 hpc1

/--
[isingBetaC_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Transition.lean)
-/
@[path]
private lemma isingBetaC_pos_eq
  {d : ℕ}
-- given
  (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
  (htransition : ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
  (hpc0 : 0 < FK.fkPc d 2)
  (hpc1 : FK.fkPc d 2 < 1) :
-- imply
  0 < IsingFK.betaC (magnetization d) := by
-- proof
  apply StatMech.Ising.isingBetaC_pos d hmag_nonneg htransition hpc0 hpc1


-- created on 2026-10-23
