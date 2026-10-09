import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.MittagLeffler

open Complex.MittagLefflerWanted

/--
[principalPart_analyticAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/MittagLeffler.lean)
-/
@[path]
private lemma principal_part_analytic_at_eq
-- given
  (s : ℂ) (coeff : ℕ →₀ ℂ) (z : ℂ) (hz : z ≠ s) :
-- imply
  AnalyticAt ℂ (principalPart s coeff) z := by
-- proof
  apply principalPart_analyticAt s coeff z hz


/--
[principalPart_meromorphicAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/MittagLeffler.lean)
-/
@[path]
private lemma principal_part_meromorphic_at_eq
-- given
  (s : ℂ) (coeff : ℕ →₀ ℂ) (x : ℂ) :
-- imply
  MeromorphicAt (principalPart s coeff) x := by
-- proof
  apply principalPart_meromorphicAt s coeff x


/--
[mittag_leffler_of_isDiscrete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/MittagLeffler.lean)
-/
@[path]
private lemma mittag_leffler_of_is_discrete_eq
-- given
  (S : Set ℂ) (hS_closed : IsClosed S)
  (hSdisc : IsDiscrete S)
  (coeff : ↥S → ℕ →₀ ℂ) :
-- imply
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Sᶜ ∧
    (∀ s : ↥S, AnalyticAt ℂ (fun z => f z - principalPart s.val (coeff s) z) s.val) ∧
    MeromorphicOn f Set.univ := by
-- proof
  apply mittag_leffler_of_isDiscrete S hS_closed hSdisc coeff


/--
[mittag_leffler](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/MittagLeffler.lean)
-/
@[path]
private lemma mittag_leffler_eq
-- given
  (S : Set ℂ) (hS_closed : IsClosed S)
  (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅)
  (coeff : ↥S → ℕ →₀ ℂ) :
-- imply
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Sᶜ ∧
    (∀ s : ↥S, AnalyticAt ℂ (fun z => f z - principalPart s.val (coeff s) z) s.val) ∧
    MeromorphicOn f Set.univ := by
-- proof
  apply mittag_leffler S hS_closed hS_discrete coeff


-- created on 2026-10-09
