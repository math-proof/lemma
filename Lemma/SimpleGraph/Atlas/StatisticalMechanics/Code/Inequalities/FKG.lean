import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
open Finset StatMech


/--
[fkg_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/FKG.lean)
-/
@[path]
private lemma fkg_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {π : ConfigSpace E → ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hπ₀ : 0 ≤ π)
  (hnorm : ∑ ω, π ω = 1)
  (hπ : FKGLatticeCondition π)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ ω, π ω * f ω) * (∑ ω, π ω * g ω) ≤ ∑ ω, π ω * (f ω * g ω) := by
-- proof
  apply StatMech.fkg_inequality hπ₀ hnorm hπ hf hg

/--
[fkg_inequality_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/FKG.lean)
-/
@[path]
private lemma fkg_inequality_events_eq
  [Fintype E]
  [DecidableEq E]
  {π : ConfigSpace E → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hπ₀ : 0 ≤ π)
  (hnorm : ∑ ω, π ω = 1)
  (hπ : FKGLatticeCondition π)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (∑ ω, π ω * A.indicator (fun _ => (1 : ℝ)) ω) * (∑ ω, π ω * B.indicator (fun _ => (1 : ℝ)) ω) ≤ ∑ ω, π ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.fkg_inequality_events hπ₀ hnorm hπ hA hB

/--
[holley_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/FKG.lean)
-/
@[path]
private lemma holley_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {μ₁ μ₂ : ConfigSpace E → ℝ}
  {t : ConfigSpace E → ℝ}
-- given
  (h₁ : 0 ≤ μ₁)
  (h₂ : 0 ≤ μ₂)
  (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
  (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b))
  (ht : Monotone t)
  (ht0 : 0 ≤ t) :
-- imply
  ∑ ω, t ω * μ₁ ω ≤ ∑ ω, t ω * μ₂ ω := by
-- proof
  apply StatMech.holley_inequality h₁ h₂ hsum hcond ht ht0

/--
[holley_dominates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/FKG.lean)
-/
@[path]
private lemma holley_dominates_eq
  [Fintype E]
  [DecidableEq E]
  {μ₁ μ₂ : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (h₁ : 0 ≤ μ₁)
  (h₂ : 0 ≤ μ₂)
  (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
  (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b))
  (hA : IsIncreasing A) :
-- imply
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * μ₁ ω ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * μ₂ ω := by
-- proof
  apply StatMech.holley_dominates h₁ h₂ hsum hcond hA


-- created on 2026-10-23
