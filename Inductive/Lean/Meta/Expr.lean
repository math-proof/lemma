module

public meta import Def.Lean.Meta.CtorName
public import Class.Lean.Meta.CtorName
public import Def.Lean.Name
public import Def.Lean.BinderInfo
public import Def.Lean.Meta.Expr
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)

@[expose] public section

public inductive Binder where
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
  deriving Inhabited, BEq, Repr

#eval mkCtorName ``Binder

