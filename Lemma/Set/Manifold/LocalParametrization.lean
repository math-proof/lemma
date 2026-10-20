import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.LocalParametrization
open scoped Topology Manifold ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.LocalParametrizationWanted


/--
[_root_.ContDiff.isImmersion_graph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/LocalParametrization.lean)
-/
@[path]
private lemma ContDiff_isImmersion_graph_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ∞ω}
  {h : E → F}
-- given
  (hh : ContDiff ℝ n h) :
-- imply
  IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, E × F) n (fun x => (x, h x)) := by
-- proof
  apply ContDiff.isImmersion_graph hh

/--
[regularLevelSet_localParametrization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/LocalParametrization.lean)
-/
@[path]
private lemma regularLevelSet_localParametrization_eq
  {k m : ℕ}
  {f : EuclideanSpace ℝ (Fin (k + m)) → EuclideanSpace ℝ (Fin m)}
  {x₀ : EuclideanSpace ℝ (Fin (k + m))}
-- given
  (hf : ContDiff ℝ 1 f)
  (hreg : Function.Surjective (fderiv ℝ f x₀)) :
-- imply
  ∃ (U : Set (EuclideanSpace ℝ (Fin k))) (_ : IsOpen U)
    (u₀ : EuclideanSpace ℝ (Fin k)) (_ : u₀ ∈ U)
    (φ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin (k + m))),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + m))) 1 φ ∧
    IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (k + m))) 1 φ ∧
    ∃ V ∈ 𝓝 x₀, φ '' (U ∩ φ ⁻¹' V) = V ∩ f ⁻¹' {f x₀} ∧ φ u₀ = x₀ := by
-- proof
  apply MathlibExt.Geometry.Manifold.LocalParametrizationWanted.regularLevelSet_localParametrization f hf x₀ hreg


-- created on 2026-10-20
