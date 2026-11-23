module

public import Mathlib.Tactic
public import Theorem.Bool.Or.of.Or.Imp
public import Theorem.Bool.And.of.And.Imp
public import Theorem.Bool.Imp.is.ImpNotS
public import Theorem.Bool.Imp.of.Imp.Imp
public import Def.Lean.Meta.Expr -- using Lean.Expr.is_Prop
public import Def.Lean.FVarId
public import Syntax.Tactic.Logic.Part3

@[expose] public meta section

open Lean Elab.Tactic Meta Parser.Tactic


@[tactic denote]
meta def evalDenote : Tactic
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

