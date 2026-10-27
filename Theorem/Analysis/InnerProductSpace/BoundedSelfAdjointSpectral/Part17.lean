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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part17
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

theorem spectralMulEquiv_cyclic
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (g : Lp ℂ 2 (spectralMulMeasure T hT (i : E))) :
    spectralMulEquiv T hT (spectralMulCyclicIsometry T hT (i : E) g) =
      spectralMulFiberIsometry T hT i g := by
  classical
  rw [← (spectralMulIsHilbertSum T hT).linearIsometryEquiv_symm_apply_single g]
  change (spectralMulFiberIsHilbertSum T hT).linearIsometryEquiv.symm
      ((spectralMulIsHilbertSum T hT).linearIsometryEquiv
        ((spectralMulIsHilbertSum T hT).linearIsometryEquiv.symm (lp.single 2 i g))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    (spectralMulFiberIsHilbertSum T hT).linearIsometryEquiv_symm_apply_single]

theorem spectralMulEquiv_intertwines
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (x : E) :
    spectralMulEquiv T hT (T x) =
      spectralMulGlobalLpOperator T hT (spectralMulEquiv T hT x) := by
  let A : E →L[ℂ] Lp ℂ 2 (spectralMulSumMeasure T hT) :=
    (spectralMulEquiv T hT).toLinearIsometry.toContinuousLinearMap.comp T
  let B : E →L[ℂ] Lp ℂ 2 (spectralMulSumMeasure T hT) :=
    (spectralMulGlobalLpOperator T hT).comp
      (spectralMulEquiv T hT).toLinearIsometry.toContinuousLinearMap
  let N : Submodule ℂ E := LinearMap.ker (A - B).toLinearMap
  let K : Submodule ℂ E :=
    ⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulCyclicIsometry T hT (i : E)).toLinearMap
  have hKN : K ≤ N := by
    apply iSup_le
    intro i
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    change (A - B) (spectralMulCyclicIsometry T hT (i : E) g) = 0
    rw [sub_apply]
    dsimp [A, B]
    change spectralMulEquiv T hT
        (T (spectralMulCyclicIsometry T hT (i : E) g)) -
      spectralMulGlobalLpOperator T hT
        (spectralMulEquiv T hT (spectralMulCyclicIsometry T hT (i : E) g)) = 0
    rw [sub_eq_zero, ← spectralMulCyclicIsometry_intertwines,
      spectralMulEquiv_cyclic, spectralMulEquiv_cyclic,
      spectralMulGlobalLpOperator_fiber]
  have hKclosure : K.topologicalClosure = ⊤ := by
    have hKorth : Kᗮ = ⊥ := spectralMulIndexSet_total T hT
    rw [← K.orthogonal_orthogonal_eq_closure, hKorth,
      Submodule.bot_orthogonal_eq_top]
  have hNtop : N = ⊤ := by
    apply top_unique
    have hclosure_le : K.topologicalClosure ≤ N :=
      K.topologicalClosure_minimal hKN (A - B).isClosed_ker
    simpa [hKclosure] using hclosure_le
  have hxN : x ∈ N := by rw [hNtop]; exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hxN
  change (A - B) x = 0 at hxN
  rw [sub_apply] at hxN
  dsimp [A, B] at hxN
  change spectralMulEquiv T hT (T x) -
    spectralMulGlobalLpOperator T hT (spectralMulEquiv T hT x) = 0 at hxN
  exact sub_eq_zero.mp hxN

namespace InnerProductSpace.BoundedSelfAdjointSpectralWanted

/--
Spectral theorem for bounded self-adjoint operators, multiplication-operator form: a
self-adjoint `T : E →L[ℂ] E` is unitarily equivalent to multiplication by a real-valued
measurable function on some `L²`. Sources: Mathlib
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` TODO (spectral theory for bounded
self-adjoint operators); W. Rudin, Functional Analysis, 2nd ed., Ch. 12.

Proves `Wanted` entry `boundedSelfAdjoint_spectral_multiplication`.

Proof: Scalar measures from the continuous functional calculus identify each cyclic subspace with an
`L²` space. A maximal orthogonal family of cyclic subspaces is then assembled over a disjoint-union
measure, where the spectral coordinate acts by multiplication.
-/
theorem boundedSelfAdjoint_spectral_multiplication
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (φ : X → ℝ) (_ : Measurable φ)
      (U : E ≃ₗᵢ[ℂ] Lp ℂ 2 μ),
      ∀ x, ∀ᵐ a ∂μ, U (T x) a = (φ a : ℂ) * U x a := by
  refine ⟨spectralMulSpace T hT, spectralMulMeasurableSpace T hT,
    spectralMulSumMeasure T hT, (fun x => (x.2 : ℂ).re), ?_, spectralMulEquiv T hT, ?_⟩
  · exact Complex.measurable_re.comp (measurable_subtype_coe.comp measurable_snd)
  · intro x
    filter_upwards [spectralMulGlobalLpOperator_ae T hT (spectralMulEquiv T hT x)]
      with a ha
    rw [spectralMulEquiv_intertwines T hT x, ha]
    have him : (a.2 : ℂ).im = 0 := hT.im_eq_zero_of_mem_spectrum a.2.property
    have hz : (a.2 : ℂ) = ((a.2 : ℂ).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hz]
    simp

end InnerProductSpace.BoundedSelfAdjointSpectralWanted
end
