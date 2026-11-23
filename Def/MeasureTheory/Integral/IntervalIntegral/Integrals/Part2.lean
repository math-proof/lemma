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
public import Notation.MeasureTheory.Integral.IntervalIntegral.Integrals

@[expose] public section

open Tensor


/-- `Tensor α s` is equivalent to `List.Vector α s.prod` via `Tensor.data`. -/
def Tensor.equivData (α : Type*) (s : List ℕ) : Tensor α s ≃ List.Vector α s.prod :=
  ⟨Tensor.data, Tensor.mk, fun _ => rfl, fun _ => rfl⟩

/-- `Tensor α s` is equivalent to `Fin s.prod → α`. -/
def Tensor.equivFinArrow (α : Type*) (s : List ℕ) : Tensor α s ≃ (Fin s.prod → α) :=
  (Tensor.equivData α s).trans (Equiv.vectorEquivFin α s.prod)

