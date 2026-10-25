import Mathlib
import Mathlib.Data.Real.Sign
import Abbrev.Analysis.Section_9_3.Part2
import Theorem.Analysis.Section_9_4.Part2
/-!
# Analysis I, Section 9.5: Left and right limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits.
-/


namespace Chapter9

/-- Definition 9.5.1.  We give left and right limits the "junk" value of 0 if the limit does not exist. -/
abbrev RightLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: LeftLimitExists X f x₀ then h.choose else 0

end Chapter9
