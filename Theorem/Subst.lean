module
public import Abbrev.Subst
public import Syntax.Subst


/--
`Subst` is reducible, so `Subst f a = f a` holds by `rfl`.
-/
@[simp]
public theorem Subst.eq_app {α : Sort*} {β : Sort*} (f : α → β) (a : α) : «Subst» f a = f a :=
  rfl


-- created on 2026-11-23
