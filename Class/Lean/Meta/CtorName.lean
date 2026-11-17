module

public import Lean
public section

open Lean Elab Command Parser.Term


class CtorName (α : Type u) where
  ctorName : α → String

