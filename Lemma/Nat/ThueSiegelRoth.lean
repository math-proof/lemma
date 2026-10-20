import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ThueSiegelRoth
open MathlibExt.NumberTheory.ThueSiegelRothWanted


/--
[thue_siegel_roth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ThueSiegelRoth.lean)
-/
@[path]
private lemma thue_siegel_roth_eq
  :
-- imply
  ∀ (α : ℝ), IsAlgebraic ℚ α → Irrational α →
    ∀ (ε : ℝ), 0 < ε →
    Set.Finite { q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + ε) } := by
-- proof
  apply MathlibExt.NumberTheory.ThueSiegelRothWanted.thue_siegel_roth


-- created on 2026-10-20
