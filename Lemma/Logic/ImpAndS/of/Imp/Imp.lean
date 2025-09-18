import Lemma.Logic.Imp_And.of.Imp.Imp
import Lemma.Logic.Imp.of.Imp.Imp
open Logic


@[main]
private lemma main
-- given
  (h₀ : p₀ → q₀)
  (h₁ : p₁ → q₁) :
-- imply
  p₀ ∧ p₁ → q₀ ∧ q₁ := by
-- proof
  apply Imp_And.of.Imp.Imp
  ·
    have : p₀ ∧ p₁ → p₀ := by tauto
    exact Imp.of.Imp.Imp this h₀
  ·
    have : p₀ ∧ p₁ → p₁ := by tauto
    exact Imp.of.Imp.Imp this h₁


-- created on 2025-04-10
