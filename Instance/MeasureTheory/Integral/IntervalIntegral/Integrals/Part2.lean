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
public import Def.MeasureTheory.Integral.IntervalIntegral.Integrals.Part2
@[expose] public section

open Tensor


/-- Scalar multiplication on `Tensor α s` via elementwise multiplication. -/
instance [Mul α] : SMul α (Tensor α s) where
  smul r X := ⟨X.data.map (r * ·)⟩

