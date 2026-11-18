module

public meta import Def.Lean.Meta.CtorName
public import Class.Lean.Meta.CtorName

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
