import Lean

/-
Canonical `⬝ᵥ` notation for `Dot.dot`.

Same precedence, associativity, and notation priority as the former local
declarations `infixl:72 (priority := 2000) " ⬝ᵥ " => Dot.dot`.

`Dot.dot` is resolved at the use site so this module does not pick a particular
`Dot` class (`Class.Data.Fin.Dot` vs `Class.Data.Vector.Basic`). Importing this
file does not pull in those classes, which would otherwise clash.
-/

/- The syntax name is `termDotV`, not Mathlib's auto-generated `«term_⬝ᵥ_»` (`Mathlib.Data.Matrix.Mul` already owns that name via `infixl:72 " ⬝ᵥ " => dotProduct`). A distinct name lets this declaration coexist with Mathlib's; `priority := 2000` makes our parser take precedence at use sites, matching the former local `infixl`s. -/
syntax:72 (name := termDotV) (priority := 2000) term:72 " ⬝ᵥ " term:73 : term

open Lean Elab Term in
/-- Elaborate `x ⬝ᵥ y` as `Dot.dot x y`, looking up `Dot` in the caller's scope. -/
@[term_elab termDotV]
def elabDotV : TermElab := fun stx expectedType? =>
  match stx with
  | `($x ⬝ᵥ $y) => do
      let dot := mkIdent `Dot.dot
      elabTerm (← `($dot $x $y)) expectedType?
  | _ => throwUnsupportedSyntax
