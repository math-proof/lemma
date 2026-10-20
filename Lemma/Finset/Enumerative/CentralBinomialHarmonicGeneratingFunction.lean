import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CentralBinomialHarmonicGeneratingFunction
open MetaMathlibExt


/--
[hasSum_centralBinomial_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CentralBinomialHarmonicGeneratingFunction.lean)
-/
@[path]
private lemma hasSum_centralBinomial_harmonic_eq
  {x : ℝ}
-- given
  (hx : |x| < 1 / 4) :
-- imply
  HasSum
    (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * (harmonic (n + 1) : ℝ) *
    x ^ (n + 1))
    (2 / Real.sqrt (1 - 4 * x) *
    Real.log ((1 + Real.sqrt (1 - 4 * x)) / (2 * Real.sqrt (1 - 4 * x)))) := by
-- proof
  apply MetaMathlibExt.hasSum_centralBinomial_harmonic x hx


-- created on 2026-10-20
