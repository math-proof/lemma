import Mathlib.Topology.ContinuousOn
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (h₀ : ContinuousOn f (Set.Icc a b))
  {xi : ℝ}
  (h₁ : xi ∈ Set.Icc a b) :
-- imply
  Filter.Tendsto f (nhdsWithin xi (Set.Icc a b)) (nhds (f xi)) :=
-- proof
  h₀ xi h₁


-- created on 2020-05-01
-- updated on 2026-10-26
