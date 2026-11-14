import Lean

/-
Scoped sugar: apply a function to a random variable by juxtaposition.

In `open scoped ApplyRV`, `g b` elaborates as `Function.applyRV g b`
(i.e. `g ∘ b`) when `g : β → γ` and `b : Ω → β`. Ordinary application
`g x` with `x : β` is unchanged: this elaborator only fires when the
argument's type is an arrow whose *codomain* is the domain of `g`, so
it does not steal `g : (Ω → β) → γ` applied to `b : Ω → β`.

This is not a `Coe ℝ (Ω → ℝ)` and does not lift `+`; open this scope
explicitly (it is not part of `open scoped ProbabilityTheory`).
-/
/-- Apply a function to a random variable: `applyRV g b` is `g ∘ b`.
Kept as its own (reducible) constant so Infoview can pretty-print it as
`g b` without rewriting ordinary `Function.comp`. -/
@[reducible] def Function.applyRV {Ω : Sort _} {β : Sort _} {γ : Sort _} (g : β → γ) (b : Ω → β) : Ω → γ :=
  g ∘ b

@[simp] theorem Function.applyRV_apply {Ω : Sort _} {β : Sort _} {γ : Sort _} (g : β → γ) (b : Ω → β) (ω : Ω) :
    Function.applyRV g b ω = g (b ω) :=
  rfl

/-- Infoview: print `Function.applyRV g b` as `g b`.
Over-application uses parentheses so `(g b) ω` does not re-parse as a
two-argument application of `g`. Ordinary `g ∘ h` is not rewritten. -/
@[app_unexpander Function.applyRV]
def Function.applyRV.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $g $b) => `($g $b)
  | `($_ $g $b $ω) => `(($g $b) $ω)
  | _ => throw ()

namespace ApplyRV

open Lean Meta Elab Term

/-- Scoped application elaborator: `g b` ~> `Function.applyRV g b`
when `g : β → γ` and `b : Ω → β`, and this is not ordinary application. -/
@[scoped term_elab Lean.Parser.Term.app]
def elabAppApplyRV : TermElab := fun stx expectedType? =>
  match stx with
  | `($gStx $bStx) => do
    let g ← try withoutErrToSorry (elabTerm gStx none) catch _ => throwUnsupportedSyntax
    let b ← try withoutErrToSorry (elabTerm bStx none) catch _ => throwUnsupportedSyntax
    let tg ← whnfR (← instantiateMVars (← inferType g))
    let tb ← whnfR (← instantiateMVars (← inferType b))
    let some (β, γ) := tg.arrow? | throwUnsupportedSyntax
    let some (Ω, β') := tb.arrow? | throwUnsupportedSyntax
    unless (← withoutModifyingState (isDefEq β β')) do throwUnsupportedSyntax
    -- Ordinary application: the argument already has type `β`.
    if (← withoutModifyingState (isDefEq tb β)) then throwUnsupportedSyntax
    let Ω ← instantiateMVars Ω
    let β ← instantiateMVars β
    let γ ← instantiateMVars γ
    let g ← instantiateMVars g
    let b ← instantiateMVars b
    let result ← try
        let uΩ ← getLevel Ω
        let uβ ← getLevel β
        let uγ ← getLevel γ
        let result := mkAppN (mkConst ``Function.applyRV [uΩ, uβ, uγ]) #[Ω, β, γ, g, b]
        let result ← instantiateMVars result
        if result.hasExprMVar then throwUnsupportedSyntax
        pure result
      catch _ => throwUnsupportedSyntax
    match expectedType? with
    | some exp =>
      unless (← withoutModifyingState (isDefEq (← inferType result) exp)) do
        throwUnsupportedSyntax
      ensureHasType expectedType? result
    | none =>
      pure result
  | _ => throwUnsupportedSyntax

end ApplyRV
