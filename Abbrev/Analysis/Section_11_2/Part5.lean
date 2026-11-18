module

public import Mathlib
public import Instance.Analysis.Section_11_1.Part8
public import Abbrev.Analysis.Section_11_2.Part4
public import Abbrev.Analysis.Section_11_1.Part2
@[expose] public noncomputable section
/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/


namespace Chapter11

open BoundedInterval

/-- Example 11.2.4 / Example 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- junk value
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- junk value

/-- Definition 11.2.9 (Piecewise constant integral I). -/
noncomputable abbrev PiecewiseConstantWith.integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * J.length

end Chapter11
