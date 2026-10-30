import Def.Lean.Level
import Def.Lean.Name
import Def.Data.List.List.Basic
import Def.Lean.Expr.Part11
import Def.Lean.PrettyPrinter.Latex
open Lean (Name)
set_option linter.unusedVariables false


inductive ExpectationView where
  | map (f rv : Expr)
  | mapBody (body rv μ : Expr)
  | cond (f x y : Expr)
  | condBody (body x y μ : Expr)
  /-- `Expectation.condSigma` (`𝔼[x: π](f x | y t, z)`) and the partial forms `partialRV*`
  (`𝔼[x: π | y](…)`): stretchy `\middle|` followed by the conditioners `ys` (magenta random arguments;
  the observed variable of `partialRV_cond` stays red). -/
  | condSigma (f x : Expr) (ys : List Expr)
  | condSigmaBody (body x : Expr) (ys : List Expr) (μ : Expr)

