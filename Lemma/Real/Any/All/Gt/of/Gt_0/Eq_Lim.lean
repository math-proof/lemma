import Lemma.Real.EqLim.is.All_Any_All_LtAbsSub
import sympy.concrete.quantifier
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Real


@[main]
private lemma main
  (f : ℝ → ℝ)
  (x₀ A : ℝ)
-- given
  (hA : 0 < A)
  (h : lim [x → x₀] f x = A) :
-- imply
  ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, f x > A / 2 := by
-- proof
  obtain ⟨δ, hδ, hδ'⟩ :=
    All_Any_All_LtAbsSub.of.EqLim.εδ h (A / 2) (by linarith)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hε : |f x - A| < A / 2 := hδ' x hx
  rw [abs_lt] at hε
  linarith


-- created on 2026-09-26
