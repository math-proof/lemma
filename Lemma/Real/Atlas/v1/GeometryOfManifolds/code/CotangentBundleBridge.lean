import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.CotangentBundleBridge
open DifferentialFormSpace CotangentBundle


/--
[proj_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CotangentBundleBridge.lean)
-/
@[path]
private lemma proj_mk_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {x : M}
  {ξ : TangentSpace I x →ₗ[ℝ] ℝ} :
-- imply
  proj I M (mk I M x ξ) = x := by
-- proof
  apply CotangentBundle.proj_mk I M x ξ


-- created on 2026-10-23
