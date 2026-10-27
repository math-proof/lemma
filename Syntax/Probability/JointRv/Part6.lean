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
import Def.Probability.JointRv.Part8
open MeasureTheory
open scoped ProbabilityTheory


open Lean


elab_rules : term
  | `(𝔼[$xs:ident,* : $π]($body)) => do
      let xs := xs.getElems
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.ofRV $π $joint $lam)
  | `(𝔼[$xs:ident,* : $π]($body | $y:term = $y0)) => do
      let xs := xs.getElems
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.condEvent $π $joint $y $lam $y0)
  | `(𝔼[$xs:ident,* : $π]($body | $y:term = $y0:term ∧ $[$ys:term = $ys0:term]∧*)) => do
      let xs := xs.getElems
      -- `y = y0 ∧ z = z0 ∧ …` ↦ `JointRandomSymbol y (JointRandomSymbol z …)` at `(y0, z0, …)`
      let conds := #[y] ++ ys
      let vals := #[y0] ++ ys0
      let mut cond : Term := conds.back!
      let mut val : Term := vals.back!
      for i in (List.range (conds.size - 1)).reverse do
        cond ← `(JointRandomSymbol $(conds[i]!) $cond)
        val ← `(($(vals[i]!), $val))
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.condEvent $π $joint $cond $lam $val)
  | `(𝔼[$xs:ident,* : $π]($body | $ys,*)) => do
      let xs := xs.getElems
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      let cond ← Lean.Elab.liftMacroM <| Expectation.Macro.mkJointTerms ys.getElems
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.condSigma $π $joint $cond $lam)
  | `(𝔼[$xs:ident,* : $π:expectMeasure | $ys,*]($body | $r:term = $r0)) => do
      let π ← Lean.Elab.liftMacroM <| Expectation.Macro.measure π
      let xs := xs.getElems
      let ys := ys.getElems
      -- Same alias threading as `elabExpect` (partial forms previously skipped `desugarProbRA`).
      let aliases ← Expectation.Macro.mkOuterAliases (xs ++ ys)
      let body' ← Lean.Elab.liftMacroM <| Expectation.Macro.desugarProbRA aliases body
      let maskX ← Expectation.Macro.rebindMask xs body'
      let maskY ← Expectation.Macro.rebindMask ys body'
      let funX ← Expectation.Macro.funBinderMask xs
      let funY ← Expectation.Macro.funBinderMask ys
      let integ ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      let free ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint ys
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest ys nestY ⟨body'⟩ maskY funY
      let bodyXY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest xs nestX bodyY maskX funX
      let lam ← if maskX.any id then
          if maskY.any id then `(fun $nestX $nestY ↦ $bodyXY) else `(fun $nestX _ ↦ $bodyXY)
        else
          if maskY.any id then `(fun _ $nestY ↦ $bodyXY) else `(fun _ _ ↦ $bodyXY)
      let core ← `(Expectation.partialRV_cond $π $integ $free $r $lam $r0)
      let wrapped ← Lean.Elab.liftMacroM <| Expectation.Macro.wrapAliases aliases core
      Lean.Elab.Term.elabTerm wrapped none
  | `(𝔼[$xs:ident,* : $π:expectMeasure | $ys,*]($body)) => do
      let π ← Lean.Elab.liftMacroM <| Expectation.Macro.measure π
      let xs := xs.getElems
      let ys := ys.getElems
      let aliases ← Expectation.Macro.mkOuterAliases (xs ++ ys)
      let body' ← Lean.Elab.liftMacroM <| Expectation.Macro.desugarProbRA aliases body
      let maskX ← Expectation.Macro.rebindMask xs body'
      let maskY ← Expectation.Macro.rebindMask ys body'
      let funX ← Expectation.Macro.funBinderMask xs
      let funY ← Expectation.Macro.funBinderMask ys
      let integ ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      let free ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint ys
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest ys nestY ⟨body'⟩ maskY funY
      let bodyXY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest xs nestX bodyY maskX funX
      let lam ← if maskX.any id then
          if maskY.any id then `(fun $nestX $nestY ↦ $bodyXY) else `(fun $nestX _ ↦ $bodyXY)
        else
          if maskY.any id then `(fun _ $nestY ↦ $bodyXY) else `(fun _ _ ↦ $bodyXY)
      let core ← `(Expectation.partialRV $π $integ $free $lam)
      let wrapped ← Lean.Elab.liftMacroM <| Expectation.Macro.wrapAliases aliases core
      Lean.Elab.Term.elabTerm wrapped none

