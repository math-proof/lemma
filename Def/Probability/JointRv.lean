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
open MeasureTheory
open scoped ProbabilityTheory


/--
[sympy.JointRandomSymbol](https://github.com/sympy/sympy/blob/master/sympy/stats/joint_rv.py)
-/
def JointRandomSymbol
    {Ω α β : Type*}
    (x : Ω → α) (y : Ω → β) :
    Ω → α × β :=
  fun ω ↦ (x ω, y ω)


