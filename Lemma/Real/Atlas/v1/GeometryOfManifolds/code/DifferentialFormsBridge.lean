import Mathlib
import sympy.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialFormsBridge.Part2
open MfdDiffForm
open scoped Manifold


namespace MfdDiffForm

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialFormsBridge.lean)
-/
@[path]
lemma ext
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ω η : MfdDiffForm k I M}
-- given
  (h : ∀ x, ω x = η x) :
-- imply
  ω = η :=
-- proof
  funext h

end MfdDiffForm

namespace MfdDiffForm

/--
[pullbackForm_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DifferentialFormsBridge.lean)
-/
@[path]
lemma pullbackForm_id
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  [IsManifold I ⊤ M]
  {k : ℕ}
  {ω : MfdDiffForm k I M} :
-- imply
  pullbackForm (I := I) (J := I) id ω = ω := by
-- proof
  funext x
  simp only [pullbackForm, id, mfderiv_id]
  exact AlternatingMap.compLinearMap_id (ω x)
/-- Naturality of the exterior derivative: $f^*(d\omega) = d(f^*\omega)$ for smooth `f`. -/

end MfdDiffForm


-- created on 2026-10-23
