import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Def.MeasureTheory.Integral.IntervalIntegral.Integrals.Part2
open Tensor


/-- Scalar multiplication on `Tensor α s` via elementwise multiplication. -/
instance [Mul α] : SMul α (Tensor α s) where
  smul r X := ⟨X.data.map (r * ·)⟩

