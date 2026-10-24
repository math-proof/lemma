/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LegendreSymbol/EisensteinJacobiSymbol.lean -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

namespace MetaMathlibExt

/-! # Eisenstein's lemma for Jacobi symbols
-/

private def eisS (a b : ℕ) : ℕ := ∑ x ∈ Finset.Ico 1 (b / 2).succ, a * x / b

private def gaussCount (m b : ℕ) : ℕ :=
  {x ∈ Finset.Ico 1 (b / 2).succ | b / 2 < (m * x) % b}.card
end MetaMathlibExt
