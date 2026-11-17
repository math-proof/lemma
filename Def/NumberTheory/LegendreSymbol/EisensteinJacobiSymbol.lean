/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LegendreSymbol/EisensteinJacobiSymbol.lean -/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas

@[expose] public section

namespace MetaMathlibExt

/-! # Eisenstein's lemma for Jacobi symbols
-/

def eisS (a b : ℕ) : ℕ := ∑ x ∈ Finset.Ico 1 (b / 2).succ, a * x / b

def gaussCount (m b : ℕ) : ℕ :=
  {x ∈ Finset.Ico 1 (b / 2).succ | b / 2 < (m * x) % b}.card

end MetaMathlibExt
