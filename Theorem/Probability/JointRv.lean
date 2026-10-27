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
import Instance.Probability.JointRv.Part2
open MeasureTheory
open scoped ProbabilityTheory


/-- `AsPathRV.path` is the identity on an ordinary random variable. -/
@[simp] theorem AsPathRV.path_function {Ω α : Type*} (f : Ω → α) :
    AsPathRV.path f = f :=
  rfl

/-- `AsPathRV.path` flips a process to its path-valued random variable. -/
@[simp] theorem AsPathRV.path_process {Ω α : Type*} (X : ℕ → Ω → α) :
    AsPathRV.path X = fun ω t ↦ X t ω :=
  rfl

/-- `AsPathRV.path` flips a `Fun` process to its path-valued random variable. -/
@[simp] theorem AsPathRV.path_fun {Ω α : Type*} (f : Fun ℕ (Ω → α)) :
    AsPathRV.path f = fun ω t ↦ f.toFun t ω :=
  rfl

