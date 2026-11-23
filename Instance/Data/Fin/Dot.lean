module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Notation.Fun
public import Notation.Data.Fin.Dot

@[expose] public section

/-- Finite dot product: `v ⬝ᵥ w = ∑ i, v i * w i`. -/
instance [Mul α] [AddCommMonoid α] [Fintype ι] : Dot (ι → α) (ι → α) α where
  dot := dotProduct

