import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Lindemann
open MathlibExt.NumberTheory.LindemannWanted


/--
[hermite_lindemann](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Lindemann.lean)
-/
@[path]
private lemma hermite_lindemann_eq
  :
-- imply
  ∀ (α : ℂ), α ≠ 0 → IsAlgebraic ℚ α → Transcendental ℚ (Complex.exp α) := by
-- proof
  apply MathlibExt.NumberTheory.LindemannWanted.hermite_lindemann


-- created on 2026-10-20
