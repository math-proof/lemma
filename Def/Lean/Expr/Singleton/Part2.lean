import Def.Lean.Name
import Mathlib.Basic.Real.Basic
import Instance.Lean.Expr.Singleton
open Lean


def Constant.toLatex : Constant → String
  | True => "\\top"
  | False => "\\bot"
  | NaN => "\\mathrm{NaN}"
  | EmptySet => "\\emptyset"
  | UniversalSet => "\\mathbb{U}"
  | Pi => "\\pi"
  | ImaginaryUnit => "\\color{blue}\\text{I}"
  | Nat => "\\mathbb{N}"
  | Int => "\\mathbb{Z}"
  | Rat => "\\mathbb{Q}"
  | Real => "\\mathbb{R}"
  | Complex => "\\mathbb{C}"
  | true => "true"
  | false => "false"
  | natVal val => s!"{val}"
  | ident name =>
    match name with
    | `EmptyCollection.emptyCollection => "\\emptyset"
    | `List.nil => "[]"
    | `Hyperreal.epsilon => "0^+"
    | `Hyperreal.omega => "\\infty"
    | _ => name.escape_specials "."


