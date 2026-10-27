import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Def.MeasureTheory.Integral.IntervalIntegral.Integrals.Part4
open Tensor


/-- `Tensor ℝ s` is finite-dimensional over `ℝ` (via `equivFinArrowL`). -/
instance : FiniteDimensional ℝ (Tensor ℝ s) :=
  FiniteDimensional.of_injective
    (Tensor.equivFinArrowL ℝ s).toLinearMap
    (Tensor.equivFinArrow ℝ s).injective

