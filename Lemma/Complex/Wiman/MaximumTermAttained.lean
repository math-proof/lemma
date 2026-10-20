import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.MaximumTermAttained
open Filter Set
open Complex


/--
[bddAbove_range_wimanTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
private lemma bddAbove_range_wimanTerm_eq
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  BddAbove (range (wimanTerm f r)) := by
-- proof
  apply Complex.bddAbove_range_wimanTerm f hf r

/--
[wimanTerm_le_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
private lemma wimanTerm_le_wimanMaximumTerm_eq
  {f : ℂ → ℂ}
  {r : ℝ}
  {n : ℕ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTerm f r n ≤ wimanMaximumTerm f r := by
-- proof
  apply Complex.wimanTerm_le_wimanMaximumTerm f hf r n

/--
[wimanMaximumTerm_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
private lemma wimanMaximumTerm_le_iff_eq
  {f : ℂ → ℂ}
  {r a : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanMaximumTerm f r ≤ a ↔ ∀ n : ℕ, wimanTerm f r n ≤ a := by
-- proof
  apply Complex.wimanMaximumTerm_le_iff f hf r a

/--
[exists_wimanTerm_eq_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermAttained.lean)
-/
@[path]
private lemma exists_wimanTerm_eq_wimanMaximumTerm_eq
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  ∃ n : ℕ, wimanTerm f r n = wimanMaximumTerm f r := by
-- proof
  apply Complex.exists_wimanTerm_eq_wimanMaximumTerm f hf r


-- created on 2026-10-20
