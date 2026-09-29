import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  {π : Measure Ω}
  {x : Ω → α}
  {f g : α → ℝ}
-- given
  [PSpace π x]
  (h : ∀ a, f a = g a) :
-- imply
  𝔼[x: π](f x) = 𝔼[x: π](g x) := by
-- proof
  simp only [h]


-- created on 2026-09-27
