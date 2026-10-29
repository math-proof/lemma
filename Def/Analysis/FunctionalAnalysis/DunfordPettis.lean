/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/DunfordPettis.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin
import Lemma.Set.IsCompact.is.IsSeqCompact
import Lemma.Real.FunctionalAnalysis.MilmanPettis
open MeasureTheory
open scoped ENNReal
open scoped Pointwise


namespace MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted

open Filter Topology

/-- The `L² → L¹` inclusion as a continuous linear map. -/
noncomputable def dpcLpTwoToLpOneCLM
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] :
    (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 1 μ) :=
  LinearMap.mkContinuous
    { toFun := fun g => ((Lp.memLp g).mono_exponent one_le_two).toLp (⇑g)
      map_add' := fun g₁ g₂ => by
        change ((Lp.memLp (g₁ + g₂)).mono_exponent one_le_two).toLp (⇑(g₁ + g₂)) =
          ((Lp.memLp g₁).mono_exponent one_le_two).toLp (⇑g₁) +
            ((Lp.memLp g₂).mono_exponent one_le_two).toLp (⇑g₂)
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_add g₁ g₂)
      map_smul' := fun c g => by
        change ((Lp.memLp (c • g)).mono_exponent one_le_two).toLp (⇑(c • g)) =
          c • ((Lp.memLp g).mono_exponent one_le_two).toLp (⇑g)
        rw [← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Lp.coeFn_smul c g) }
    ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) (fun g => by
      have hmem : AEStronglyMeasurable (⇑g) μ := (Lp.memLp g).aestronglyMeasurable
      have hfin : eLpNorm (⇑g) 2 μ ≠ ⊤ := (Lp.memLp g).eLpNorm_lt_top.ne
      have hle : eLpNorm (⇑g) 1 μ ≤
          eLpNorm (⇑g) 2 μ *
            μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two hmem
      have hexp : 1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal = 1 / 2 := by
        rw [ENNReal.toReal_one, ENNReal.toReal_ofNat]
        norm_num
      have hMfin :
          μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) ≠ ⊤ := by
        rw [hexp]
        exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by finiteness)).ne
      have h2norm : ‖g‖ = (eLpNorm (⇑g) 2 μ).toReal := by
        conv_lhs => rw [← Lp.toLp_coeFn g (Lp.memLp g)]
        exact Lp.norm_toLp _ _
      calc ‖((Lp.memLp g).mono_exponent one_le_two).toLp (⇑g)‖
            = (eLpNorm (⇑g) 1 μ).toReal := Lp.norm_toLp _ _
          _ ≤ (eLpNorm (⇑g) 2 μ *
              μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hMfin) hle
          _ = (μ Set.univ).toReal ^ (1 / 2 : ℝ) * (eLpNorm (⇑g) 2 μ).toReal := by
              rw [ENNReal.toReal_mul, hexp, ← ENNReal.toReal_rpow, mul_comm]
          _ = (μ Set.univ).toReal ^ (1 / 2 : ℝ) * ‖g‖ := by rw [h2norm])

/-- Set integrals as elements of the dual of `L¹`. -/
noncomputable def dpcSetIntegralL1CLM
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (s : Set α) :
    StrongDual ℝ (Lp ℝ 1 μ) :=
  L1.integralCLM.comp (LpToLpRestrictCLM α ℝ ℝ μ 1 s)

end MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted
