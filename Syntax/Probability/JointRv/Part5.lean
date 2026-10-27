import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Def.Probability.SymbolicProbability.Part2
import Theorem.Function
import Def.Probability.JointRv.Part7
open MeasureTheory
open scoped ProbabilityTheory


open Lean


/-- RA slots are `term:51` (idents, apps `a t`, and GetElem `a[t]`); observation forms keep
`term:max "=" term:lead` so `x = x0` is never swallowed by the RA parsers. -/
syntax:max "ℙ[" term "]" "(" term:51,+ ")" : term

syntax:max "ℙ[" term "]" "(" term:51,+ "|" term:51,+ ")" : term

syntax:max "ℙ[" term "]" "(" term:51,+ "|" sepBy1(term:max "=" term:lead, "∧") ")" : term

syntax:max "ℙ[" term "]" "(" sepBy1(term:max "=" term:lead, "∧") ")" : term

syntax:max "ℙ[" term "]" "(" sepBy1(term:max "=" term:lead, "∧") "|" sepBy1(term:max "=" term:lead, "∧") ")" : term

syntax:max "ℙ[" term "]" "(" sepBy1(term:max "=" term:lead, "∧") "|" term:51,+ ")" : term

