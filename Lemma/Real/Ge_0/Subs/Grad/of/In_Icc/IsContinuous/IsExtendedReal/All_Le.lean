import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hc : c ∈ Set.Ioo a b)
  (_ : ContinuousOn f (Set.Icc a b))
  (_ : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (hle : ∀ x ∈ Set.Icc a b, f x ≤ f c) :
-- imply
  deriv f c ≥ 0 := by
-- proof
  have hmax : IsLocalMax f c :=
    (isMaxOn_iff.mpr fun x hx => hle x hx).isLocalMax (Icc_mem_nhds hc.1 hc.2)
  have := hmax.deriv_eq_zero
  linarith


-- created on 2023-10-15
-- updated on 2026-10-12
