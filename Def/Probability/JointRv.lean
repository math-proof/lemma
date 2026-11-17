module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Def.Probability.SymbolicProbability
public import Theorem.Function

@[expose] public section

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


