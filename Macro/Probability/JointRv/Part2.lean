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
import Syntax.Probability.JointRv.Part5
open MeasureTheory
open scoped ProbabilityTheory


open Lean


macro_rules
  | `(ℙ[$π]($xs:term,*)) => do
      let x ← Probability.Macro.mkJointRV xs
      `(Measure.probRA $π $x)
  | `(ℙ[$π]($xs:term,* | $ys:term,*)) => do
      let x ← Probability.Macro.mkJointRV xs
      let y ← Probability.Macro.mkJointRV ys
      `(Measure.probCondRA $π (JointRandomSymbol $x $y))
  | `(ℙ[$π]($xs:term,* | $[$y:term = $y0:term]∧*)) => do
      let x ← Probability.Macro.mkJointRV xs
      let y ← Probability.Macro.mkJointRV y
      let y0 ← Probability.Macro.mkProd y0
      `(Measure.probCond $π (JointRandomSymbol $x $y) $y0)
  | `(ℙ[$π]($[$x:term = $x0:term]∧*)) => do
      let x ← Probability.Macro.mkJointRV x
      let x0 ← Probability.Macro.mkProd x0
      `(Measure.prob $π $x $x0)
  | `(ℙ[$π]($[$x:term = $x0:term]∧* | $[$y:term = $y0:term]∧*)) => do
      let x ← Probability.Macro.mkJointRV x
      let x0 ← Probability.Macro.mkProd x0
      let y ← Probability.Macro.mkJointRV y
      let y0 ← Probability.Macro.mkProd y0
      `(Measure.condProb $π (JointRandomSymbol $x $y) ($x0, $y0))
  | `(ℙ[$π]($[$x:term = $x0:term]∧* | $ys:term,*)) => do
      let x ← Probability.Macro.mkJointRV x
      let x0 ← Probability.Macro.mkProd x0
      let y ← Probability.Macro.mkJointRV ys
      `(Measure.condProbRA $π (JointRandomSymbol $x $y) $x0)

