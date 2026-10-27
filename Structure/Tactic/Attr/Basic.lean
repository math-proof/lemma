import Mathlib.Tactic
import Def.Lean.Syntax
import Def.Lean.Environment
import Def.Lean.Meta.Expr.Part4
import Def.Lean.ConstantInfo.Part5
import Def.Tactic.Attr.Basic
open Lean
open Lean.Meta


structure EventuallyLayer where
  us : List Level
  α : Lean.Expr
  binderName : Name
  binderType : Lean.Expr
  binderInfo : BinderInfo
  f : Lean.Expr

