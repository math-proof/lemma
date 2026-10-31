import Syntax.Logic.Quantifier.Part4
import Def.Analysis.Real.Limits.Basic
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Set Filter


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : Tendsto f (nhdsWithin x₀ {x₀}ᶜ) atBot) :
-- imply
  ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, f x < 0 := by
-- proof
  have hev := eventually_nhdsWithin_iff.mp (h.eventually_lt_atBot 0)
  obtain ⟨δ, hδ, H⟩ := Metric.nhds_basis_ball.eventually_iff.mp hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  apply H
  · simpa [Real.dist_eq] using hx.2
  · exact sub_ne_zero.mp (abs_pos.mp hx.1)


-- created on 2023-10-15
-- updated on 2026-10-26
