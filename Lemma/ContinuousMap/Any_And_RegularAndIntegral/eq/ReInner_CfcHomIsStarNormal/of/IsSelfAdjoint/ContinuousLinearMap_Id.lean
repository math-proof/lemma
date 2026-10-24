import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.BoundedSelfAdjointSpectral

open MeasureTheory


/--
[BoundedSelfAdjointSpectral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/BoundedSelfAdjointSpectral.lean)
-/
@[path]
private lemma exists_spectralMeasure_eq
-- given
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (T : ContinuousLinearMap (RingHom.id ℂ) E E)
  (hT : IsSelfAdjoint T)
  (v : E) :
-- imply
  ∃ μ : Measure (spectrum ℂ T), IsFiniteMeasure μ ∧ μ.Regular ∧
    ∀ f : ContinuousMap (spectrum ℂ T) ℝ,
      ∫ z, f z ∂μ = Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
        (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
          ContinuousMap (spectrum ℂ T) ℂ) v) v) := by
-- proof
  apply IsSelfAdjoint.exists_spectralMeasure T hT v

-- created on 2026-10-10
