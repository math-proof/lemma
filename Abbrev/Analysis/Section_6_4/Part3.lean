import Mathlib
import Abbrev.Analysis.Section_6_3
import Theorem.Analysis.Section_6_4.Part2


namespace Chapter6

open EReal

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

end Chapter6
