import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.Sard
open scoped Manifold ContDiff Topology ENNReal MeasureTheory
open MeasureTheory
open MathlibExt.Geometry.Manifold.SardWanted


/--
[sard_euclidean_open](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/Sard.lean)
-/
@[path]
private lemma sard_euclidean_open_eq
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [μ.IsAddHaarMeasure]
  {U : Set E}
  {g : E → F}
-- given
  (hU : IsOpen U)
  (hg : ContDiffOn ℝ ∞ g U) :
-- imply
  μ (g '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0 := by
-- proof
  apply MathlibExt.Geometry.Manifold.SardWanted.sard_euclidean_open E F μ U hU g hg

/--
[sard_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/Sard.lean)
-/
@[path]
private lemma sard_theorem_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))] [BorelSpace (EuclideanSpace ℝ (Fin n))]
  {f : M → EuclideanSpace ℝ (Fin n)}
-- given
  (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) f) :
-- imply
  volume (criticalValues (I := by
-- proof
  apply MathlibExt.Geometry.Manifold.SardWanted.sard_theorem f hf


-- created on 2026-10-20
