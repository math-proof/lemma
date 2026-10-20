import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.HilbertSymbol.Units
open HilbertSymbol


/--
[chevalley_warning_hensel_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Units.lean)
-/
@[path]
private lemma chevalley_warning_hensel_lift_eq
  {p : ℕ} [Fact p.Prime]
  {u v : ℤ_[p]ˣ}
-- given
  (hp_odd : p ≠ 2) :
-- imply
  ∃ (x₀ y₀ : ℤ_[p]) (z₀ : ℤ_[p]ˣ),
    (z₀ : ℤ_[p]) ^ 2 = (u : ℤ_[p]) * x₀ ^ 2 + (v : ℤ_[p]) * y₀ ^ 2 := by
-- proof
  apply HilbertSymbol.chevalley_warning_hensel_lift p hp_odd u v

/--
[hilbert_symbol_units_eq_one_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Units.lean)
-/
@[path]
private lemma hilbert_symbol_units_eq_one_of_odd_eq
  {p : ℕ} [Fact p.Prime]
  {u v : ℤ_[p]ˣ}
-- given
  (hp_odd : p ≠ 2) :
-- imply
  padicHilbertSymbol p (unitZpToQp u) (unitZpToQp v) = 1 := by
-- proof
  apply HilbertSymbol.hilbert_symbol_units_eq_one_of_odd p hp_odd u v


-- created on 2026-10-20
