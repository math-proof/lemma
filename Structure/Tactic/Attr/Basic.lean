module

public import Mathlib.Tactic
public section

open Lean
open Lean.Meta


structure EventuallyLayer where
  us : List Level
  α : Lean.Expr
  binderName : Name
  binderType : Lean.Expr
  binderInfo : BinderInfo
  f : Lean.Expr

