module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Theorem.Vector.Zero.eq.Replicate
public import Theorem.Tensor.Eq.is.EqDataS
public import Instance.Data.Tensor.Tensor.Part2
public import Instance.MeasureTheory.Integral.IntervalIntegral.Integrals.Part2

@[expose] public section

open Tensor


/-- `Tensor α s` as an `AddMonoidHom` to `Fin s.prod → α` (using natural `Add`/`Zero`). -/
def Tensor.toAddMonoidHom (α : Type*) (s : List ℕ) [AddMonoid α] :
    Tensor α s →+ (Fin s.prod → α) where
  toFun := Tensor.equivFinArrow α s
  map_zero' := by
    funext j
    simp only [Tensor.equivFinArrow, Tensor.equivData, Equiv.vectorEquivFin,
      Equiv.trans_apply, Equiv.coe_fn_mk]
    exact List.Vector.get_replicate 0 j
  map_add' := fun X Y => by
    funext j
    simp only [Tensor.equivFinArrow, Tensor.equivData, Equiv.vectorEquivFin,
      Equiv.trans_apply, Equiv.coe_fn_mk]
    show (X.data.map₂ HAdd.hAdd Y.data).get j = X.data.get j + Y.data.get j
    rw [List.Vector.get_map₂]

