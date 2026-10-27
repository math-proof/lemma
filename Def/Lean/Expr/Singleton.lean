import Def.Lean.Name
import Mathlib.Basic.Real.Basic
import Inductive.Lean.Expr.Singleton
open Lean


def Constant.toString : Constant → String
  | True => "True"
  | False => "False"
  | NaN => "NaN"
  | EmptySet => "∅"
  | UniversalSet => "UniversalSet"
  | Pi => "π"
  | ImaginaryUnit => "ImaginaryUnit"
  | Nat => "ℕ"
  | Int => "ℤ"
  | Rat => "ℚ"
  | Real => "ℝ"
  | Complex => "ℂ"
  | true => "true"
  | false => "false"
  | natVal val => s!"{val}"
  | ident name =>
    match name with
    | `EmptyCollection.emptyCollection => "∅"
    | `List.nil => "[]"
    | _ => name.toString


