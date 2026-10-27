import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Inductive.Lean.Expr.Part2
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def ExprWithAttr.func : ExprWithAttr → Func
  | Lean_function name =>
    let name := name.getLast.toString
    ⟨75, name, "\\" ++ name⟩
  | Lean_operatorname name =>
    let name := name.getLast.toString
    ⟨
      75,
      name,
      "\\operatorname{%s}".format name.escape_specials
    ⟩
  | Lean_typeclass name =>
    let name := name.getLast.toString
    ⟨
      75,
      name,
      "\\text{\\color{#708}%s}".format name.escape_specials
    ⟩
  | LeanLemma name =>
    let name := name.getLast.toString
    ⟨75, "⋯", "\\cdots"⟩
  | LeanMethod name idx =>
    let name := name.getLast.toString
    ⟨75, s!"%s.{name} %s", s!"%s.{name.escape_specials}\\ %s"⟩
  | LeanProperty name =>
    let name := name.getLast.toString
    ⟨81, s!".{name}", s!".{name.escape_specials}"⟩


def ExprWithAttr.name : ExprWithAttr → Name
  | Lean_function name
  | Lean_operatorname name
  | Lean_typeclass name
  | LeanLemma name
  | LeanMethod name idx
  | LeanProperty name => name


def ExprWithAttr.isProp : ExprWithAttr → Bool
  | .LeanProperty `IsConstant.is_constant => true
  | _ => false


