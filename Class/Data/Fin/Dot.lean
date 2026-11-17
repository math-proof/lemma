module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Notation.Fun


public section

class Dot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  dot : α → β → γ

