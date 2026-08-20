import sympy.concrete.quantifier
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.Eq.is.Any_All.limit_definition |
| comm | Real.Any_All.is.Eq.limit_definition |
| mp | Real.Any_All.of.Eq.limit_definition |
| mpr | Real.Eq.of.Any_All.limit_definition |
-/
@[main, comm, mp, mpr]
private lemma limit_definition
-- given
  (f : ℝ → ℝ)
  (x₀ a : ℝ) :
-- imply
  lim [x → x₀] f x = a ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, |f x - a| < ε := by
-- proof
  constructor
  ·
    intro h ε hε
    obtain ⟨δ, hδ, H⟩ := Metric.tendsto_nhdsWithin_nhds.mp h ε hε
    refine ⟨δ, hδ, fun x hx => ?_⟩
    simpa [Real.dist_eq] using H (Set.mem_compl_singleton_iff.mpr (sub_ne_zero.mp (abs_pos.mp hx.1))) (by simpa [Real.dist_eq] using hx.2)
  ·
    intro h
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    simpa [Real.dist_eq] using H x ⟨abs_pos.mpr (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hx)), by simpa [Real.dist_eq] using hxδ⟩


-- created on 2026-08-20
