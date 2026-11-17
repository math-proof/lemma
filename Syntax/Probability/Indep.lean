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
public meta import Theorem.Function
public import Theorem.Probability.JointRv.AsRV

public meta section

open MeasureTheory
open scoped ProbabilityTheory


/-- Left operand of the `⟂ᵢ` sugar: a process `X : ℕ → Ω → α` (e.g. a slice `r[t + 1:]`) becomes
its path-valued RV `Expectation.asRV X = fun ω k ↦ X k ω`; any other term is returned unchanged
(syntactically, so `rw`/`simp` patterns on ordinary RVs keep matching). -/
syntax (name := condIndepLeft) "condIndepLeft% " term:max : term


open Lean Elab Term Meta in
@[term_elab condIndepLeft] def elabCondIndepLeft : TermElab := fun stx _ => do
  match stx with
  | `(condIndepLeft% $x) =>
    let e ← Lean.Elab.Term.elabTerm x none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← whnfR (← instantiateMVars (← inferType e))
    match ty with
    | .forallE _ d b _ =>
      if d.isConstOf ``Nat && !b.hasLooseBVars && (← whnfR b).isForall then
        mkAppM ``Expectation.asRV #[e]
      else
        return e
    | _ => return e
  | _ => throwUnsupportedSyntax
