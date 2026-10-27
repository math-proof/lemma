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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part13
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

theorem spectralMulFiberOrthogonalFamily
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    OrthogonalFamily ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (spectralMulFiberIsometry T hT) := by
  intro i j hij f g
  rw [L2.inner_def, ← integral_zero]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i f),
    MemLp.coeFn_toLp (spectralMulExtend_memLp T hT j g)] with x hf hg
  change inner ℂ
    ((((spectralMulExtend_memLp T hT i f).toLp
      (spectralMulExtend T hT i f)) : spectralMulSpace T hT → ℂ) x)
    ((((spectralMulExtend_memLp T hT j g).toLp
      (spectralMulExtend T hT j g)) : spectralMulSpace T hT → ℂ) x) = 0
  rw [hf, hg]
  by_cases hi : x.1 = i
  · have hj : x.1 ≠ j := fun hj => hij (hi.symm.trans hj)
    have hxi : x ∈ spectralMulFiber T hT i := hi
    have hxj : x ∉ spectralMulFiber T hT j := hj
    simp [spectralMulExtend, Set.indicator_of_mem hxi, Set.indicator_of_notMem hxj]
  · have hxi : x ∉ spectralMulFiber T hT i := hi
    simp [spectralMulExtend, Set.indicator_of_notMem hxi]

theorem spectralMulFiber_ae_zero_of_mem_orthogonal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (F : Lp ℂ 2 (spectralMulSumMeasure T hT))
    (hF : F ∈ (⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap)ᗮ)
    (i : spectralMulIndexSet T hT) :
    ∀ᵐ z ∂spectralMulMeasure T hT (i : E), F (i, z) = 0 := by
  have hFrestrict :
      MemLp (F : spectralMulSpace T hT → ℂ) 2 (spectralMulFiberMeasure T hT i) :=
    MemLp.mono_measure
      (by
        rw [spectralMulSumMeasure]
        exact Measure.le_sum _ i)
      (Lp.memLp F)
  have hFcomp : MemLp (fun z => F (i, z)) 2 (spectralMulMeasure T hT (i : E)) := by
    have hmap : MemLp (F : spectralMulSpace T hT → ℂ) 2
        (Measure.map (Prod.mk i) (spectralMulMeasure T hT (i : E))) := by
      simpa [spectralMulFiberMeasure] using hFrestrict
    have hcomp := (measurableEmbedding_prodMk_left i).memLp_map_measure_iff.mp hmap
    simpa [Function.comp_def] using hcomp
  let g : Lp ℂ 2 (spectralMulMeasure T hT (i : E)) :=
    hFcomp.toLp (fun z => F (i, z))
  have hg : (g : spectrum ℂ T → ℂ) =ᵐ[spectralMulMeasure T hT (i : E)]
      fun z => F (i, z) := by
    exact MemLp.coeFn_toLp hFcomp
  have hJ :
      ((spectralMulFiberIsometry T hT i g : Lp ℂ 2 (spectralMulSumMeasure T hT)) :
          spectralMulSpace T hT → ℂ) =ᵐ[spectralMulSumMeasure T hT]
        spectralMulExtend T hT i (fun z => F (i, z)) := by
    exact (MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i g)).trans
      (spectralMulExtend_congr_ae T hT i hg)
  have hinner : inner ℂ F (spectralMulFiberIsometry T hT i g) = 0 := by
    exact ((⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap).mem_orthogonal' F).mp
        hF _ ((le_iSup (fun i : spectralMulIndexSet T hT =>
          LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap) i)
            (LinearMap.mem_range_self _ g))
  have hinner_self :
      inner ℂ (spectralMulFiberIsometry T hT i g)
          (spectralMulFiberIsometry T hT i g) =
        inner ℂ F (spectralMulFiberIsometry T hT i g) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
    rcases x with ⟨j, z⟩
    by_cases hji : j = i
    · subst j
      simp [spectralMulExtend, spectralMulFiber]
    · simp [spectralMulExtend, spectralMulFiber, hji]
  have hJzero : spectralMulFiberIsometry T hT i g = 0 :=
    inner_self_eq_zero.mp (hinner_self.trans hinner)
  have hgzero : g = 0 := by
    apply (spectralMulFiberIsometry T hT i).injective
    simpa using hJzero
  rw [hgzero] at hg
  filter_upwards [hg, Lp.coeFn_zero ℂ 2 (spectralMulMeasure T hT (i : E))] with z hz hz0
  rw [← hz]
  exact hz0

theorem spectralMulFiber_iSup_orthogonal_eq_bot
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    (⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap)ᗮ = ⊥ := by
  apply le_antisymm
  · intro F hF
    rw [Submodule.mem_bot]
    apply Lp.ext
    have hmeas : MeasurableSet
        {x : spectralMulSpace T hT | (F : spectralMulSpace T hT → ℂ) x = 0} := by
      exact (MeasurableSet.singleton 0).preimage (Lp.stronglyMeasurable F).measurable
    have hzero : ∀ᵐ x ∂spectralMulSumMeasure T hT, F x = 0 := by
      change ∀ᵐ x ∂Measure.sum (spectralMulFiberMeasure T hT), F x = 0
      rw [Measure.ae_sum_iff' hmeas]
      intro i
      rw [spectralMulFiberMeasure]
      apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
      exact spectralMulFiber_ae_zero_of_mem_orthogonal T hT F hF i
    filter_upwards [hzero,
      Lp.coeFn_zero ℂ 2 (spectralMulSumMeasure T hT)] with x hx hx0
    rw [hx]
    simpa using hx0.symm
  · exact bot_le

theorem spectralMulFiberIsHilbertSum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    IsHilbertSum ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (spectralMulFiberIsometry T hT) := by
  apply IsHilbertSum.mk (spectralMulFiberOrthogonalFamily T hT)
  let K : Submodule ℂ (Lp ℂ 2 (spectralMulSumMeasure T hT)) :=
    ⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulFiberIsometry T hT i).toLinearMap
  have hK : Kᗮ = ⊥ := spectralMulFiber_iSup_orthogonal_eq_bot T hT
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, hK]
    simp
  exact hclosure.ge

theorem spectralMulLpOperator_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (g : Lp ℂ 2 (spectralMulMeasure T hT v)) :
    spectralMulLpOperator T hT v g =ᵐ[spectralMulMeasure T hT v]
      fun z => (z : ℂ) * g z := by
  change (spectralMulCoordinateLp T hT v • g :
    Lp ℂ 2 (spectralMulMeasure T hT v)) =ᵐ[spectralMulMeasure T hT v] _
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralMulCoordinateLp T hT v) g,
    spectralMulCoordinateLp_ae T hT v] with z hmul hz
  rw [hmul]
  change (spectralMulCoordinateLp T hT v) z * g z = (z : ℂ) * g z
  rw [hz]

end
