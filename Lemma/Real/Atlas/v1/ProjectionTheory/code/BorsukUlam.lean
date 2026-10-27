import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.BorsukUlam
open BorsukUlam


namespace BorsukUlam

/--
[neg_mem_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BorsukUlam.lean)
-/
@[path]
lemma neg_mem_sphere
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hx : x ∈ Sphere n) :
-- imply
  -x ∈ Sphere n := by
-- proof
  simp only [Sphere, Metric.mem_sphere, dist_zero_right] at hx ⊢
  rwa [norm_neg]
/-- The Borsuk–Ulam theorem: any continuous antipodal map `f : S^n → ℝ^n`
(satisfying `f(−x) = −f(x)` for all `x ∈ S^n`) has a zero, i.e. there exists
`x ∈ S^n` with `f(x) = 0`. -/

end BorsukUlam


-- created on 2026-10-23
