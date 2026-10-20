import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.DeGuaHeron
open scoped InnerProductSpace
open MetaMathlibExt


/--
[deGua_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGuaHeron.lean)
-/
@[path]
private lemma deGua_theorem_eq
  :
-- imply
  ∀ (a b c A : ℝ),
    let p₀ := by
-- proof
  apply MetaMathlibExt.deGua_theorem


-- created on 2026-10-20
