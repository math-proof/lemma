import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.RiemannianMetricExistence
open Manifold
open Bundle Manifold
open MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted


/--
[riemannianMetricExistence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/RiemannianMetricExistence.lean)
-/
@[path]
private lemma riemannianMetricExistence_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : ℕ∞) M] :
-- imply
  Nonempty (Bundle.ContMDiffRiemannianMetric I (⊤ : ℕ∞) E (fun (x : M) => TangentSpace I x)) := by
-- proof
  apply MathlibExt.Geometry.Manifold.RiemannianMetricExistenceWanted.riemannianMetricExistence


-- created on 2026-10-20
