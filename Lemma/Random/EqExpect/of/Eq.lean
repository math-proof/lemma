import Mathlib.Probability.Independence.Integration
import Def.Probability.Moments.Variance
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
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


-- created on 2023-04-04
