module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Notation.Fun
public import Def.Data.Fin.Dot


public section

/-- `v ⬝ᵥ w` when `w` is a closed slice `f[a:b]`, whose `Fin` length need not be definitionally
the length of `v`. -/
instance (priority := low) [AddCommMonoid α] [Mul α] {m : ℕ} (s : Slice) :
    Dot (Fin m → α) (FunSlice.Out α s) α where
  dot v w := Fin.dotResize v (w : Fin (s.stop.toNat - s.start.toNat) → α)

