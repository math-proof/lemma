import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.HolleyFKG
open Finset StatMech StatMech.Probability


/--
[FKGCondition.holleyLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma holleyLatticeCondition_eq
  [Lattice α]
  {μ : α → ℝ≥0}
-- given
  (h : FKGCondition μ) :
-- imply
  HolleyLatticeCondition μ μ := by
-- proof
  apply StatMech.Probability.FKGCondition.holleyLatticeCondition h

/--
[holley_le_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma holley_le_of_monotone_eq
  [Fintype α]
  [DecidableEq α]
  [DistribLattice α]
  {μ₁ μ₂ : α → ℝ≥0}
  {t : α → ℝ}
-- given
  (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a)
  (hcond : HolleyLatticeCondition μ₁ μ₂)
  (ht : Monotone t)
  (ht0 : 0 ≤ t) :
-- imply
  ∑ a, t a * (μ₁ a : ℝ) ≤ ∑ a, t a * (μ₂ a : ℝ) := by
-- proof
  apply StatMech.Probability.holley_le_of_monotone hsum hcond ht ht0

/--
[holley_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma holley_domination_eq
  [Fintype α]
  [DecidableEq α]
  [DistribLattice α]
  {μ₁ μ₂ : α → ℝ≥0}
-- given
  (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a)
  (hcond : HolleyLatticeCondition μ₁ μ₂) :
-- imply
  StochasticDom μ₁ μ₂ := by
-- proof
  apply StatMech.Probability.holley_domination hsum hcond

/--
[holley_exists_isMonotoneCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma holley_exists_isMonotoneCoupling_eq
  [Fintype α]
  [DecidableEq α]
  [DistribLattice α]
  {μ₁ μ₂ : α → ℝ≥0}
-- given
  (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a)
  (hcond : HolleyLatticeCondition μ₁ μ₂) :
-- imply
  ∃ π : α × α → ℝ≥0, IsMonotoneCoupling μ₁ μ₂ π := by
-- proof
  apply StatMech.Probability.holley_exists_isMonotoneCoupling hsum hcond

/--
[holley_domination_iff_monotoneCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma holley_domination_iff_monotoneCoupling_eq
  [Fintype α]
  [DecidableEq α]
  [DistribLattice α]
  {μ₁ μ₂ : α → ℝ≥0}
-- given
  (hsum : ∑ a, μ₁ a = ∑ a, μ₂ a)
  (hcond : HolleyLatticeCondition μ₁ μ₂) :
-- imply
  StochasticDom μ₁ μ₂ ↔ ∃ π : α × α → ℝ≥0, IsMonotoneCoupling μ₁ μ₂ π := by
-- proof
  apply StatMech.Probability.holley_domination_iff_monotoneCoupling hsum hcond

/--
[fkg_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma fkg_inequality_eq
  [Fintype α]
  [DecidableEq α]
  [DistribLattice α]
  [OrderBot α]
  {π : α → ℝ}
  {f g : α → ℝ}
-- given
  (hπ₀ : 0 ≤ π)
  (hnorm : ∑ a, π a = 1)
  (hπ : ∀ x y, π x * π y ≤ π (x ⊓ y) * π (x ⊔ y))
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ a, π a * f a) * (∑ a, π a * g a) ≤ ∑ a, π a * (f a * g a) := by
-- proof
  apply StatMech.Probability.fkg_inequality hπ₀ hnorm hπ hf hg

/--
[fkg_conditioning_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/HolleyFKG.lean)
-/
@[path]
private lemma fkg_conditioning_domination_eq
  [Fintype α]
  [DecidableEq α]
  [DistribLattice α]
  {π : α → ℝ≥0}
  {S : Finset α}
-- given
  (hπ : FKGCondition π)
  (hS : ∀ ⦃a b⦄, a ≤ b → a ∈ S → b ∈ S) :
-- imply
  StochasticDom ((∑ a ∈ S, π a) • π) ((∑ a, π a) • restrictTo π S) := by
-- proof
  apply StatMech.Probability.fkg_conditioning_domination hπ hS


-- created on 2026-10-23
