import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
open MeasureTheory StatMech


/--
[StochasticallyDominated.refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StochasticDomination.lean)
-/
@[path]
private lemma refl_eq
  {μ : Measure (ConfigSpace E)} :
-- imply
  μ ≼ μ := by
-- proof
  apply StatMech.StochasticallyDominated.refl μ

/--
[StochasticallyDominated.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StochasticDomination.lean)
-/
@[path]
private lemma trans_eq
  {μ ν ρ : Measure (ConfigSpace E)}
-- given
  (h₁ : μ ≼ ν)
  (h₂ : ν ≼ ρ) :
-- imply
  μ ≼ ρ := by
-- proof
  apply StatMech.StochasticallyDominated.trans h₁ h₂


-- created on 2026-10-23
