import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.HadamardGlobalInverse
open scoped Manifold ContDiff
open MathlibExt.Geometry.Manifold.HadamardGlobalInverseWanted


/--
[hadamard_caccioppoli_global_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HadamardGlobalInverse.lean)
-/
@[path]
private lemma hadamard_caccioppoli_global_inverse_eq
  {n : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
-- given
  (hf_proper : IsProperMap f)
  (hf_local : IsLocalDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f) :
-- imply
  ∃ (Φ : EuclideanSpace ℝ (Fin n) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ EuclideanSpace ℝ (Fin n)), ⇑Φ = f := by
-- proof
  apply MathlibExt.Geometry.Manifold.HadamardGlobalInverseWanted.hadamard_caccioppoli_global_inverse f hf_proper hf_local


-- created on 2026-10-20
