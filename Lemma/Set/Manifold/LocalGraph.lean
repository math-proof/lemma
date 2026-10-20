import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.LocalGraph
open scoped Topology
open MathlibExt.Geometry.Manifold.LocalGraphWanted


/--
[_root_.ContDiff.exists_localGraph_of_surjective_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/LocalGraph.lean)
-/
@[path]
private lemma ContDiff_exists_localGraph_of_surjective_fderiv_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F}
  {x₀ : E}
-- given
  (hdim : Module.finrank ℝ E = Module.finrank ℝ G + Module.finrank ℝ F)
  (hf : ContDiff ℝ 1 f)
  (hreg : Function.Surjective (fderiv ℝ f x₀)) :
-- imply
  ∃ (e : E ≃L[ℝ] G × F)
    (U : Set G) (_ : U ∈ 𝓝 (e x₀).1) (g : G → F),
    ContDiffOn ℝ 1 g U ∧ ∃ V ∈ 𝓝 x₀, V ∩ f ⁻¹' {f x₀} =
    V ∩ e ⁻¹' {p : G × F | p.1 ∈ U ∧ p.2 = g p.1} := by
-- proof
  apply ContDiff.exists_localGraph_of_surjective_fderiv hdim f hf x₀ hreg

/--
[regularLevelSet_localGraph](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/LocalGraph.lean)
-/
@[path]
private lemma regularLevelSet_localGraph_eq
  {k m : ℕ}
  {f : EuclideanSpace ℝ (Fin (k + m)) → EuclideanSpace ℝ (Fin m)}
  {x₀ : EuclideanSpace ℝ (Fin (k + m))}
-- given
  (hf : ContDiff ℝ 1 f)
  (hreg : Function.Surjective (fderiv ℝ f x₀)) :
-- imply
  ∃ (e : EuclideanSpace ℝ (Fin (k + m)) ≃L[ℝ]
    (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)))
    (U : Set (EuclideanSpace ℝ (Fin k))) (_ : U ∈ 𝓝 ((e x₀).1))
    (g : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    ContDiffOn ℝ 1 g U ∧ ∃ V ∈ 𝓝 x₀, V ∩ f ⁻¹' {f x₀}
    = V ∩ e ⁻¹' {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) |
    p.1 ∈ U ∧ p.2 = g p.1} := by
-- proof
  apply MathlibExt.Geometry.Manifold.LocalGraphWanted.regularLevelSet_localGraph f hf x₀ hreg


-- created on 2026-10-20
