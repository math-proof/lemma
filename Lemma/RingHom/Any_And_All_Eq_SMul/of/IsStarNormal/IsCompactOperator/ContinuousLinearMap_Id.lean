import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.CompactSpectral


/--
[CompactSpectral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/CompactSpectral.lean)
-/
@[path]
private lemma compactNormal_hilbertBasis_eq
-- given
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (T : ContinuousLinearMap (RingHom.id ℂ) E E)
  (hT_compact : IsCompactOperator T)
  (hT_normal : IsStarNormal T) :
-- imply
  ∃ (ι : Type u) (b : HilbertBasis ι ℂ E) (μ : ι → ℂ),
    (∀ ε > (0 : ℝ), Set.Finite { i | ε ≤ ‖μ i‖ }) ∧ (∀ i, T (b i) = μ i • b i) := by
-- proof
  apply InnerProductSpace.CompactSpectralWanted.compactNormal_hilbertBasis T hT_compact hT_normal


-- created on 2026-10-10
-- updated on 2026-10-26
