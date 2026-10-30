import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Notation.Fun
import Def.Data.Fin.Dot


/-- `v @ w` when `w` is a closed slice `f[a:b]`, whose `Fin` length need not be definitionally
the length of `v`. -/
instance (priority := low) [AddCommMonoid α] [Mul α] {m : ℕ} (s : Slice) :
    Dot (Fun (Fin m) α) (FunSlice.Out α s) α where
  dot v w := Fin.dotResize v.toFun (w : Fin (s.stop.toNat - s.start.toNat) → α)

