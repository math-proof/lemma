module

public meta import Lean
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public meta import Syntax.Probability.Expectation.Elab
public meta import Syntax.Data.List
public import Def.Data.List.List.Basic
public import Instance.Analysis.Real.Numbers
public import Notation.Fun
public import Instance.Probability.Process.HiddenMarkovSequence.Part2

public meta section

open MeasureTheory
open scoped ENNReal.ToRealCoe

open MeasureTheory
open scoped ENNReal.ToRealCoe


open Lean in
macro_rules
  | `(($x, $ys,*)[:$n]) => do
    let comps ← (#[x] ++ ys.getElems).mapM fun z => `($z i)
    let tuple : Term ← if comps.size ≤ 3 then
        `(($(comps[0]!), $(comps.extract 1 comps.size),*))
      else
        comps.pop.foldrM (fun c acc => `(JointRandomSymbol $c $acc)) comps.back!
    `(fun ω (i : Fin $n) ↦ $tuple ω)
