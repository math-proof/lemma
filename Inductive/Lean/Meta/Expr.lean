import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
import Def.Lean.Meta.Expr
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


inductive Binder where
  /-- explicit binder annotation for proposition, e.g. `(h : Prop)` -/
  | given
  /-- Default binder annotation, e.g. `(x : α)` -/
  | default
  /-- Implicit binder annotation, e.g., `{x : α}` -/
  | implicit
  /-- Strict implicit binder annotation, e.g., `{{ x : α }}` -/
  | strictImplicit
  /-- Local instance binder annotataion, e.g., `[Decidable α]` -/
  | instImplicit
  /-- membership binder annotation, e.g. `x ∈ α` -/
  | contains
  deriving Inhabited, BEq, Repr, CtorName

