import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part17
open MeasureTheory


/--
[BoundedSelfAdjointSpectral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/BoundedSelfAdjointSpectral.lean)
-/
@[path]
private lemma boundedSelfAdjoint_spectral_multiplication_eq
-- given
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (T : ContinuousLinearMap (RingHom.id ℂ) E E)
  (hT : IsSelfAdjoint T) :
-- imply
  ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (φ : X → ℝ) (_ : Measurable φ) (U : LinearIsometryEquiv (RingHom.id ℂ) E (Lp ℂ 2 μ)),
    ∀ x, ∀ᵐ a ∂μ, U (T x) a = (φ a : ℂ) * U x a := by
-- proof
  apply InnerProductSpace.BoundedSelfAdjointSpectralWanted.boundedSelfAdjoint_spectral_multiplication T hT


-- created on 2026-10-10
-- updated on 2026-10-26
