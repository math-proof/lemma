import stdlib.Lean.Name
open Lean

inductive Constant where
  | True
  | False
  | NaN
  | EmptySet
  | UniversalSet
  | Pi
  | ImaginaryUnit
  | Nat
  | Int
  | Rat
  | Real
  | Complex
  | true
  | false
  | natVal (val : Nat)
  | ident (name : Name)
  deriving Repr, BEq, Inhabited


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


instance : ToString Constant where
  toString := Constant.toString


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
