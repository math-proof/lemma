import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.HilbertSymbol.Isotropic
open HilbertSymbol


/--
[diagonal_unit_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Isotropic.lean)
-/
@[path]
private lemma diagonal_unit_isotropic_eq
  {p : ℕ} [Fact p.Prime]
  {n : ℕ}
  {a : Fin n → ℤ_[p]ˣ}
-- given
  (hp_odd : p ≠ 2)
  (hn : 2 < n) :
-- imply
  ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, ((a i : ℤ_[p]) : ℚ_[p]) * (x i) ^ 2 = 0 := by
-- proof
  apply HilbertSymbol.diagonal_unit_isotropic p hp_odd hn a


-- created on 2026-10-20
