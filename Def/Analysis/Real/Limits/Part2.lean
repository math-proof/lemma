import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part6
open Lean
open scoped Topology


partial def unparenTerm? : Syntax → Syntax
  | `(term| ($t)) => t
  | stx => stx

partial def asTendsToZero? : Syntax → Option Syntax
  | `($x → 0) => some x
  | stx =>
    match unparenTerm? stx with
    | `($x → 0) => some x
    | _ => none

partial def asTendsToInf? : Syntax → Option Syntax
  | `($x → ∞) => some x
  | stx =>
    match unparenTerm? stx with
    | `($x → ∞) => some x
    | _ => none

@[app_unexpander And]
def tendsToPosNeg.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    match a with
    | `(0 < $x) =>
      match asTendsToInf? b with
      | some y =>
        if x == y then
          let y : TSyntax `term := ⟨y⟩
          `($y → +∞)
        else
          throw ()
      | none =>
        match asTendsToZero? b with
        | some y =>
          if x == y then
            let y : TSyntax `term := ⟨y⟩
            `($y → 0⁺)
          else
            throw ()
        | none => throw ()
    | `($x < $zero) =>
      match zero with
      | `(0) =>
        match asTendsToInf? b with
        | some y =>
          if x == y then
            let y : TSyntax `term := ⟨y⟩
            `($y → -∞)
          else
            throw ()
        | none =>
          match asTendsToZero? b with
          | some y =>
            if x == y then
              let y : TSyntax `term := ⟨y⟩
              `($y → 0⁻)
            else
              throw ()
          | none => throw ()
      | _ =>
        throw ()
    | _ =>
      throw ()
  | _ =>
    throw ()

