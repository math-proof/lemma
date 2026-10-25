/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticGaussSumFive.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark (Muse Spark 1.3)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.LegendreSymbol
/-!
# Quadratic Gauss sum modulo five

For an integer `k`, the quadratic Gauss sum `g(k; 5)` is the finite sum
`∑_{n=0}^{4} exp (2 * π * I * k * n ^ 2 / 5)`.

Provenance: Greg Dresden and Yike Li, "Periodic Weighted Sums of Binomial
Coefficients," Journal of Integer Sequences 26 (2023), source TeX
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Dresden/dresden26.tex>,
lines 284–291, which defines `g(k; 5)` as above and records the evaluation
`g(k; 5) = (k / 5) * √5` for `k` not a multiple of five. That evaluation is
classical; the JIS source cites Berndt, Evans, and Williams, Theorem 1.5.2,
and this module makes no claim that the JIS authors originated it.
-/


namespace MetaMathlibExt

/-- Primality of `5` for the Legendre-symbol API. Scoped (not global), so
importers only see it under `open scoped MetaMathlibExt`. -/
scoped instance : Fact (Nat.Prime 5) := ⟨by decide⟩

end MetaMathlibExt
