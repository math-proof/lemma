/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find


namespace IntegerComplexity

/-- Inductive syntax for expressions built from `1`, `+`, `*` with parentheses
    determined by tree structure. Source C2. -/
inductive Expr where
  | one : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving DecidableEq, Repr

end IntegerComplexity
