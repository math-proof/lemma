import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Def.Fun
import Notation.Data.Fin.Dot


/-- Finite dot product: `v @ w = ∑ i, v i * w i`. -/
instance [Mul α] [AddCommMonoid α] [Fintype ι] : Dot (ι → α) (ι → α) α where
  dot := dotProduct

/-- `Fin n ⇀ α` on the left against a plain vector. -/
instance [Mul α] [AddCommMonoid α] [Fintype ι] : Dot (Fun ι α) (ι → α) α where
  dot v w := dotProduct v.toFun w

