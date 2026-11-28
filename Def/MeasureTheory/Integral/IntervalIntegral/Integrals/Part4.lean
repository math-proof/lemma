module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Theorem.Vector.Zero.eq.Replicate
public import Theorem.Tensor.Eq.is.EqDataS
public import Instance.Data.Tensor.Tensor
public import Instance.MeasureTheory.Integral.IntervalIntegral.Integrals.Part3

@[expose] public section

open Tensor


/-- `Tensor α s` is linearly equivalent to `Fin s.prod → α`. -/
def Tensor.equivFinArrowL (α : Type*) (s : List ℕ) [Semiring α] :
    Tensor α s ≃ₗ[α] (Fin s.prod → α) where
  toFun := Tensor.equivFinArrow α s
  invFun := (Tensor.equivFinArrow α s).symm
  left_inv := (Tensor.equivFinArrow α s).left_inv
  right_inv := (Tensor.equivFinArrow α s).right_inv
  map_add' := (Tensor.toAddMonoidHom α s).map_add
  map_smul' := fun r X => by
    funext j
    show (X.data.map (r * ·)).get j = r * (X.data.get j)
    rw [List.Vector.get_map]

