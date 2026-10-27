import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.ManifoldIntegration
open DifferentialFormSpace
open scoped Manifold ContDiff


/--
[IsCompactOrientedManifold.compactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldIntegration.lean)
-/
@[path]
lemma IsCompactOrientedManifold.compactSpace
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ∞ M]
-- given
  (h : IsCompactOrientedManifold I M) :
-- imply
  CompactSpace M :=
-- proof
  h.compact
/-- For a compact oriented smooth manifold $(M, I)$, this produces the Stokes-style integration
data on its differential form space: the integration map $\int_M : \Omega^{\dim M}(M) \to \mathbb{R}$
and associated pairings used to formulate Stokes' theorem. -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsCompactOrientedManifold I M]
/-- The dimension $\dim M$ of the manifold $M$, as recorded by its Stokes integration data. -/


-- created on 2026-10-23
