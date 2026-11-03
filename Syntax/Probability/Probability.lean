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

/-- Event probability: `ℙ[π]{|avg - μ| < ε}` → `π.real {ω | |avg ω - μ| < ε}`.

Braces mark an event (a `Prop` after reading random variables at `ω`), as opposed to the
parenthesized RA / observation forms `ℙ[π](…)` (pmf / pdf / conditional densities).

The body is elaborated as `Ω → Prop` when possible; otherwise it is lifted like `rv%[π] …`
(so `avg : Ω → ℝ` in `|avg - μ| < ε` becomes `|avg ω - μ| < ε`). A closed `Prop` with no
random variables becomes the constant predicate. Result type is `ℝ` (`Measure.real`). -/
syntax:max (name := probEvent) "ℙ[" term "]" "{" term "}" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(probEvent| ℙ[$π]{$e}) => do
      let πe ← elabTerm π none
      synthesizeSyntheticMVarsNoPostponing
      let πe ← instantiateMVars πe
      let πty ← whnf (← instantiateMVars (← inferType πe))
      unless πty.isAppOfArity ``MeasureTheory.Measure 2 do
        throwError "ℙ event: expected a measure, got {πe}"
      let Ω := πty.appFn!.appArg!
      let predTy ← mkArrow Ω (mkSort Level.zero)
      -- Prefer `LiftRV` whenever the body names a local RV/process on `Ω` (e.g. `∑ i, x[i]`
      -- with `x : ℕ ⇀ Ω → ℝ`). Plain elaboration often succeeds as a *closed* `Prop` via
      -- Pi/`∀` instances on `Ω → ℝ` and would skip lifting; `withoutErrToSorry` would also
      -- hide failures and block the lift path.
      let mut hasRV := false
      for id in LiftRV.idents e do
        let some (fv, []) ← resolveLocalName id.getId | continue
        let ty ← instantiateMVars (← inferType fv)
        if (← LiftRV.kind Ω ty).isSome then
          hasRV := true
          break
      let pred ← do
        if hasRV then
          try
            LiftRV.lift π e (some predTy)
          catch ex =>
            try
              elabTerm e (some predTy)
            catch _ =>
              throw ex
        else
          try
            elabTerm e (some predTy)
          catch ex =>
            if let .internal id _ := ex then
              if id == postponeExceptionId then throw ex
            try
              let p ← elabTerm e (some (mkSort Level.zero))
              let p ← instantiateMVars p
              pure (mkLambda `ω BinderInfo.default Ω p)
            catch _ =>
              throw ex
      synthesizeSyntheticMVarsNoPostponing
      let pred ← instantiateMVars pred
      if pred.hasSorry then
        throwError "ℙ event: failed to elaborate event as a predicate on the sample space"
      mkAppM ``MeasureTheory.Measure.real #[πe, ← mkAppM ``Set.ofPred #[pred]]
