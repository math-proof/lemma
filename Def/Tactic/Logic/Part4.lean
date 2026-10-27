import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import Def.Lean.Meta.Expr.Part4 -- using Lean.Expr.is_Prop
import Def.Lean.FVarId
import Syntax.Tactic.Logic.Part3
open Lean Elab.Tactic Meta Parser.Tactic


@[tactic denote]
def evalDenote : Tactic
| `(tactic| denote $h_t : $lhs = $rhs) => do
  withMainContext do
    match lhs.raw with
    | .ident _ _ val _ =>
      match val with
      | `left =>
        haveDeclaration h_t ⟨rhs.raw⟩ (← Conv.getLhs) true
      | `right =>
        haveDeclaration h_t ⟨rhs.raw⟩ (← Conv.getRhs) true
      | _ =>
        match rhs.raw with
        | .ident _ _ val _ =>
          let e ←
            match val with
            | `left => Conv.getLhs
            | `right => Conv.getRhs
            | _ => elabTermForApply rhs
          haveDeclaration h_t ⟨lhs.raw⟩ e false
        | .node _ `Lean.Parser.Term.hole #[.atom _ "_"] =>
          letAssignment h_t ⟨lhs.raw⟩ false
        | .node .. =>
          haveDeclaration h_t ⟨lhs.raw⟩ (← elabTermForApply rhs) false
        | _ =>
          throwError "denote: invalid syntax, rhs `{rhs}` must be one of left, right, _ or term"
    | .node _ `Lean.Parser.Term.hole #[.atom _ "_"] =>
      letAssignment h_t ⟨rhs.raw⟩ true
    | .node _ _ _ =>
      haveDeclaration h_t ⟨rhs.raw⟩ (← elabTermForApply lhs) true
    | _ =>
      throwError "denote: invalid syntax, lhs `{lhs}` must be one of left, right, _ or term"
| stx => do
  throwError "invalid syntax: {stx}"

