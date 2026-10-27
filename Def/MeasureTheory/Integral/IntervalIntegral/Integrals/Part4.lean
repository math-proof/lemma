import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Instance.MeasureTheory.Integral.IntervalIntegral.Integrals.Part3
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

