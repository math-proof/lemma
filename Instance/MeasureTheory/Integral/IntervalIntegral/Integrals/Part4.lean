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
public import Def.MeasureTheory.Integral.IntervalIntegral.Integrals.Part4
open Tensor


public section

/-- `Tensor ℝ s` is finite-dimensional over `ℝ` (via `equivFinArrowL`). -/
instance : FiniteDimensional ℝ (Tensor ℝ s) :=
  FiniteDimensional.of_injective
    (Tensor.equivFinArrowL ℝ s).toLinearMap
    (Tensor.equivFinArrow ℝ s).injective

