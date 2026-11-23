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
public import Instance.Probability.JointRv.Part2
open MeasureTheory
open scoped ProbabilityTheory

public section

/-- `AsPathRV.path` is the identity on an ordinary random variable. -/
@[simp] theorem AsPathRV.path_function {Ω α : Type*} (f : Ω → α) :
    AsPathRV.path f = f :=
  rfl

/-- `AsPathRV.path` flips a process to its path-valued random variable. -/
@[simp] theorem AsPathRV.path_process {Ω α : Type*} (X : ℕ → Ω → α) :
    AsPathRV.path X = fun ω t ↦ X t ω :=
  rfl

