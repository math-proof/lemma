import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Instance.MeasureTheory.Integral.IntervalIntegral.Integrals.Part2
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

