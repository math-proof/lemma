/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Order.Zorn
import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part12
open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal

/-!
# Multiplication form of the spectral theorem

This file constructs scalar spectral measures for bounded self-adjoint operators, realizes their
cyclic subspaces as `L²` spaces, and combines a maximal orthogonal family of cyclic subspaces into
the multiplication-operator form of the spectral theorem.
-/


noncomputable section

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

universe u

set_option maxHeartbeats 800000 in
-- Elaborating the dependent `L²` fiber extension needs a larger heartbeat budget.
noncomputable def spectralMulFiberIsometry
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    Lp ℂ 2 (spectralMulMeasure T hT (i : E)) →ₗᵢ[ℂ]
      Lp ℂ 2 (spectralMulSumMeasure T hT) := by
  refine
    { toFun := fun f => (spectralMulExtend_memLp T hT i f).toLp
        (spectralMulExtend T hT i f)
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro f g
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i (f + g)),
      MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f),
      MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i g),
      Lp.coeFn_add ((spectralMulExtend_memLp T hT i f).toLp
        (spectralMulExtend T hT i f))
        ((spectralMulExtend_memLp T hT i g).toLp (spectralMulExtend T hT i g)),
      spectralMulExtend_congr_ae T hT i (Lp.coeFn_add f g)] with x hfg hf hg hadd hin
    rw [hfg, hadd, Pi.add_apply, hf, hg, hin]
    by_cases hx : x ∈ spectralMulFiber T hT i
    · simp [spectralMulExtend, Set.indicator_of_mem hx]
    · simp [spectralMulExtend, Set.indicator_of_notMem hx]
  · intro c f
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i (c • f)),
      MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f),
      Lp.coeFn_smul c ((spectralMulExtend_memLp T hT i f).toLp
        (spectralMulExtend T hT i f)),
      spectralMulExtend_congr_ae T hT i (Lp.coeFn_smul c f)] with x hcf hf hsmul hin
    rw [hcf, show (RingHom.id ℂ) c = c from rfl, hsmul, Pi.smul_apply, hf, hin]
    by_cases hx : x ∈ spectralMulFiber T hT i
    · simp [spectralMulExtend, Set.indicator_of_mem hx]
    · simp [spectralMulExtend, Set.indicator_of_notMem hx]
  · intro f
    change ‖(spectralMulExtend_memLp T hT i f).toLp
      (spectralMulExtend T hT i f)‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f)),
      spectralMulExtend_eLpNorm]

end
