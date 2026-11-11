import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Notation.Fun
import Instance.Data.Fin.Dot


/-- `⬝ᵥ` as `Dot.dot` (Class.Data.Fin.Dot). Cannot import `Instance.Data.Vector.Basic.Dot` (it redefines `class Dot`). -/
infixl:72 (priority := 2000) " ⬝ᵥ " => Dot.dot

@[simp]
theorem Dot.fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v w : ι → α) :
    v ⬝ᵥ w = ∑ i, v i * w i := rfl

@[simp]
theorem Dot.fun_fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v : Fun ι α) (w : ι → α) :
    v ⬝ᵥ w = ∑ i, v.toFun i * w i := rfl

