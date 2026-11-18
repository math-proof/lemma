module

public import Inductive.Lean.Expr.Part3

@[expose] public section

open Lean (Name)

def Operator.func : Operator → Func
  | BinaryInfix op => op.func
  | UnaryPrefix op => op.func
  | UnaryPostfix op => op.func
  | ExprWithLimits op => op.func
  | Special op => op.func
  | ExprWithAttr op => op.func


def Operator.priority : Operator → Nat :=
  Func.priority ∘ Operator.func


def Operator.operator : Operator → String :=
  Func.operator ∘ Operator.func


def Operator.name : Operator → Name
  | BinaryInfix op => op.name
  | UnaryPrefix op => op.name
  | UnaryPostfix op => op.name
  | ExprWithLimits op => op.name
  | Special op => op.name
  | ExprWithAttr op => op.name


def Operator.command : Operator → String :=
  Func.command ∘ Operator.func

def Operator.methodIdx : Operator → Nat
  | ExprWithAttr (.LeanMethod _ idx) => idx
  | _ => 0
