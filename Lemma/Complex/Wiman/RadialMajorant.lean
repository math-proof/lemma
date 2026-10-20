import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.RadialMajorant
open Complex


/--
[wimanTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
private lemma wimanTerm_nonneg_eq
  {f : ℂ → ℂ}
  {r : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ wimanTerm f r n := by
-- proof
  apply Complex.wimanTerm_nonneg f r n

/--
[summable_wimanTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
private lemma summable_wimanTerm_eq
  {f : ℂ → ℂ}
  {r : ℝ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  Summable (wimanTerm f r) := by
-- proof
  apply Complex.summable_wimanTerm f hf r

/--
[wimanMajorant_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
private lemma wimanMajorant_nonneg_eq
  {f : ℂ → ℂ}
  {r : ℝ} :
-- imply
  0 ≤ wimanMajorant f r := by
-- proof
  apply Complex.wimanMajorant_nonneg f r

/--
[wimanTerm_le_wimanMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/RadialMajorant.lean)
-/
@[path]
private lemma wimanTerm_le_wimanMajorant_eq
  {f : ℂ → ℂ}
  {r : ℝ}
  {n : ℕ}
-- given
  (hf : Differentiable ℂ f) :
-- imply
  wimanTerm f r n ≤ wimanMajorant f r := by
-- proof
  apply Complex.wimanTerm_le_wimanMajorant f hf r n


-- created on 2026-10-20
