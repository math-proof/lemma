import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Notation.Fun


class Dot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  dot : α → β → γ

