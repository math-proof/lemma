import sympy.series.limits
import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  [Zero α]
  [One α]
  [NoMaxOrder α]
  [ZeroLEOneClass α]
  [NeZero (1 : α)]
-- given
  (f : α → ℝ)
  (a : ℝ)
  (h : ∀ ε > 0, ∃ N > 0, ∀ x > N, |f x - a| < ε) :
-- imply
  lim [x → ∞] f x = a := by
-- proof
  apply Metric.tendsto_atTop'.mpr
  intro ε hε
  obtain ⟨N, _, H⟩ := h ε hε
  refine ⟨N, fun x hx => ?_⟩
  simpa [Real.dist_eq] using H x hx


-- created on 2026-10-03
