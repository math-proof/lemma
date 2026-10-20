import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LandsbergSchaar
open MetaMathlibExt


/--
[landsberg_schaar](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LandsbergSchaar.lean)
-/
@[path]
private lemma landsberg_schaar_eq
  {p q : ℕ}
-- given
  (hp : 1 ≤ p)
  (hq : 1 ≤ q) :
-- imply
  (1 / (Real.sqrt (p : ℝ) : ℂ)) * ∑ n ∈ Finset.range p, Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (q : ℂ) / (p : ℂ))) =
    (Complex.exp ((Real.pi : ℂ) * Complex.I / 4) / (Real.sqrt (2 * (q : ℝ)) : ℂ)) * ∑ n ∈
    Finset.range (2 * q), Complex.exp
    (-(Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 * (p : ℂ) / (2 * (q : ℂ)))) := by
-- proof
  apply MetaMathlibExt.landsberg_schaar p q hp hq


-- created on 2026-10-20
