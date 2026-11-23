module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Notation.Fun
public import Instance.Data.Fin.Dot
public import Notation.Data.Dot

public section

@[simp]
theorem Dot.fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v w : ι → α) :
    v ⬝ᵥ w = ∑ i, v i * w i := rfl

