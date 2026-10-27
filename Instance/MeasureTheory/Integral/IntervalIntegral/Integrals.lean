import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Lemma.Vector.Zero.eq.Replicate
import Lemma.Tensor.Eq.is.EqDataS
import Instance.Data.Holor.Tensor.Part2
import Def.MeasureTheory.Integral.IntervalIntegral.Integrals
open Tensor


instance : HPow LSpace ℕ (ℝ → ℝ → Set (ℝ → ℝ)) := ⟨fun _ _ a b => {f | IntervalIntegrable f MeasureTheory.volume a b}⟩

