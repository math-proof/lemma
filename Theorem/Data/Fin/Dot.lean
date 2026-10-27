import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Def.Fun
import Instance.Data.Fin.Dot


@[simp]
theorem Dot.fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v w : ι → α) :
    v @ w = ∑ i, v i * w i := rfl

@[simp]
theorem Dot.fun_fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v : Fun ι α) (w : ι → α) :
    v @ w = ∑ i, v.toFun i * w i := rfl

