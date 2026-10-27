import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Notation.MeasureTheory.Integral.IntervalIntegral.Integrals
open Tensor


/-- `Tensor α s` is equivalent to `List.Vector α s.prod` via `Tensor.data`. -/
def Tensor.equivData (α : Type*) (s : List ℕ) : Tensor α s ≃ List.Vector α s.prod :=
  ⟨Tensor.data, Tensor.mk, fun _ => rfl, fun _ => rfl⟩

/-- `Tensor α s` is equivalent to `Fin s.prod → α`. -/
def Tensor.equivFinArrow (α : Type*) (s : List ℕ) : Tensor α s ≃ (Fin s.prod → α) :=
  (Tensor.equivData α s).trans (Equiv.vectorEquivFin α s.prod)

