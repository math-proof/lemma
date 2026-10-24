/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean -/

import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Lower
import Lemma.Nat.PrimeInterval.Breusch.Lower
import Lemma.Nat.PrimeInterval.Breusch.Theta
import Lemma.Nat.PrimeInterval.Breusch.Upper
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Theta
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Upper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Breusch's prime-interval theorem

Every real `x ≥ 48` admits a prime strictly between `x` and `(9 / 8) * x`.

Provenance: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates,
daß zwischen x und 2x stets Primzahlen liegen*, Math. Z. 34 (1932), 505–526,
conclusion on p. 515; Göttingen scan `PPN266833020_0034`, SHA-256
`0a95f2b4f7c9535740d4f88924fb5576dc31a409cfaaf524b802489804fc18f1`.
-/

namespace MathlibExt.NumberTheory.BreuschWanted

namespace Internal

/-- The assumed upper-bound shape for the endgame. -/
def upper_ineq (n : ℕ) : Prop :=
  logF9 n ≤ (18900/279 + 18900/657 + 18900/963 : ℝ) * n
    * Real.log 3.4 + Real.sqrt ((2100:ℝ)*n) * Real.log ((2100:ℝ)*n)

/-- Certified prime chain from `53` to `9820997` with ratio below `9 / 8`. -/
def chain : List ℕ :=
  [53, 59, 61, 67, 73, 79,
  83, 89, 97, 109, 113, 127,
  139, 151, 167, 181, 199, 223,
  241, 271, 293, 317, 353, 397,
  443, 491, 547, 613, 683, 761,
  853, 953, 1069, 1201, 1327, 1489,
  1669, 1877, 2111, 2371, 2663, 2971,
  3331, 3739, 4201, 4723, 5309, 5953,
  6691, 7523, 8461, 9511, 10691, 12011,
  13499, 15173, 17053, 19183, 21577, 24251,
  27281, 30689, 34519, 38833, 43669, 49123,
  55259, 62143, 69899, 78623, 88427, 99469,
  111893, 125863, 141587, 159233, 179119, 201499,
  226669, 254993, 286859, 322709, 363047, 408427,
  459479, 516911, 581521, 654209, 735983, 827969,
  931421, 1047841, 1178809, 1326151, 1491913, 1678399,
  1888193, 2124197, 2389721, 2688421, 3024457, 3402473,
  3827767, 4306231, 4844501, 5450041, 6131239, 6897643,
  7759831, 8729801, 9820997]
end Internal
end MathlibExt.NumberTheory.BreuschWanted
