module
public import Mathlib
public import Mathlib.Algebra.Field.Power
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Abbrev.Analysis.Section_6_1.Part17
public import Theorem.Analysis.Section_6_epilogue.Part2
public import Abbrev.Analysis.Section_7_2.Part5


public section

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
