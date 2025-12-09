import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
open Hyperreal


@[main]
private lemma main
  {a : ℝ*}
-- given
  (h : ¬Infinitesimal a) :
-- imply
  ∃ δ : ℝ⁺, |a| ≥ δ := by
-- proof
  contrapose! h
  apply Infinitesimal.of.All_LtAbs h


-- created on 2025-12-09
