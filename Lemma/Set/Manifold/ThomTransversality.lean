import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.ThomTransversality
open scoped Manifold
open MathlibExt.Geometry.Manifold.ThomTransversalityWanted


/--
[thom_transversality_uniform_approx_regular_value_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
private lemma thom_transversality_uniform_approx_regular_value_zero_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ}
  {f : M → EuclideanSpace ℝ (Fin n)}
  {ε : ℝ}
-- given
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
  (hε : 0 < ε) :
-- imply
  ∃ (g : M → EuclideanSpace ℝ (Fin n)),
    ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g ∧
    (∀ x : M, ‖f x - g x‖ < ε) ∧
    (∀ x : M, g x = 0 →
    Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) g x)) := by
-- proof
  apply MathlibExt.Geometry.Manifold.ThomTransversalityWanted.thom_transversality_uniform_approx_regular_value_zero f hf ε hε

/--
[thom_transversality_compact_source_uniform_approx_regular_value_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean)
-/
@[path]
private lemma thom_transversality_compact_source_uniform_approx_regular_value_zero_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ}
  {f : M → EuclideanSpace ℝ (Fin n)}
  {ε : ℝ}
-- given
  (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
  (hε : 0 < ε) :
-- imply
  ∃ (g : M → EuclideanSpace ℝ (Fin n)),
    ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g ∧
    (∀ x : M, ‖f x - g x‖ < ε) ∧
    (∀ x : M, g x = 0 →
    Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) g x)) := by
-- proof
  apply MathlibExt.Geometry.Manifold.ThomTransversalityWanted.thom_transversality_compact_source_uniform_approx_regular_value_zero f hf ε hε


-- created on 2026-10-20
