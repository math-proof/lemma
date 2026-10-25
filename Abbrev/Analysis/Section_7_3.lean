import Mathlib
import Mathlib.Algebra.Field.Power
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Abbrev.Analysis.Section_6_1.Part17
import Theorem.Analysis.Section_6_epilogue.Part2
import Abbrev.Analysis.Section_7_2.Part5
/-!
# Analysis I, Section 7.3: Sums of non-negative numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Equivalent characterizations of convergence of nonnegative series.
- Cauchy condensation test.

-/


namespace Chapter7

open Real

abbrev Series.nonneg (s: Series) : Prop := ∀ n, s.seq n ≥ 0

end Chapter7
