import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Inductive.Lean.Expr
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def ExprWithLimits.func : ExprWithLimits → Func
  | Lean_sum  => ⟨66, "∑", "\\sum"⟩
  | Lean_tsum => ⟨66, "∑'", "\\sum\\nolimits'"⟩
  | Lean_prod => ⟨71, "∏", "\\prod"⟩
  | Lean_int _ => ⟨52, "∫", "\\int"⟩
  | Lean_bigcap => ⟨52, "⋂", "\\bigcap"⟩
  | Lean_bigcup => ⟨51, "⋃", "\\bigcup"⟩
  | Lean_lim => ⟨52, "lim", "\\lim"⟩
  | Lean_sup _ => ⟨52, "sup", "\\sup"⟩
  | Lean_inf _ => ⟨52, "inf", "\\inf"⟩
  | Lean_max _ => ⟨52, "max", "\\max"⟩
  | Lean_min _ => ⟨52, "min", "\\min"⟩
  | Lean_forall => ⟨24, "∀", "\\forall"⟩
  | Lean_exists => ⟨24, "∃", "\\exists"⟩
  | Lean_lambda => ⟨72, "fun", "{\\color{magenta}fun}"⟩
  | Lean_let => ⟨47, "let", "{\\color{blue}let}"⟩

def ExprWithLimits.name : ExprWithLimits → Name
  | Lean_forall => default
  | Lean_exists => `Exists
  | Lean_sum => `Finset.sum
  | Lean_tsum => `tsum
  | Lean_prod => `Finset.prod
  | Lean_int name
  | Lean_bigcap => `Set.iInter
  | Lean_bigcup => `Set.iUnion
  | Lean_lim => `Filter.limUnder
  | Lean_sup name
  | Lean_inf name
  | Lean_max name
  | Lean_min name
  | Lean_lambda
  | Lean_let => default


def Binder.func : Binder → Func
  | implicit => ⟨47, "{%s : %s}", "\\left\\lbrace %s : %s\\right\\rbrace"⟩
  | strictImplicit => ⟨47, "⦃%s : %s⦄", "⦃%s : %s⦄"⟩
  | instImplicit => ⟨47, "[%s]", "\\left[%s\\right]"⟩
  | given => ⟨47, "(%s : %s)", "\\left(%s : %s\\right)"⟩
  | default => ⟨47, "(%s : %s)", "\\left(%s : %s\\right)"⟩
  | contains => ⟨47, "%s ∈ %s", "{%s \\in %s}"⟩


