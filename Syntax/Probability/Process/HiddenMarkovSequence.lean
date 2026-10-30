import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Syntax.Probability.JointRv.Part6
import Syntax.Data.List
import Def.Data.List.List.Basic
import Instance.Analysis.Real.Numbers
import Notation.Fun
import Instance.Probability.Process.HiddenMarkovSequence.Part2
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
