import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b c : ℝ}
-- given
  (hc : c ∈ Set.Ioo a b)
  (_ : ContinuousOn f (Set.Icc a b))
  (_ : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
  (hge : ∀ x ∈ Set.Icc a b, f x ≥ f c) :
-- imply
  deriv f c ≤ 0 := by
-- proof
  have hmin : IsLocalMin f c :=
    (isMinOn_iff.mpr fun x hx => hge x hx).isLocalMin (Icc_mem_nhds hc.1 hc.2)
  have := hmin.deriv_eq_zero
  linarith


-- created on 2023-11-10
-- updated on 2026-10-26
