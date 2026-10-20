import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LegendreSymbol.EisensteinJacobiSymbol
open MetaMathlibExt


/--
[eisenstein_lemma_jacobi_symbol_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LegendreSymbol/EisensteinJacobiSymbol.lean)
-/
@[path]
private lemma eisenstein_lemma_jacobi_symbol_general_eq
  {a b : ℕ}
-- given
  (ha_odd : Odd a)
  (hb_odd : Odd b)
  (hab : Nat.Coprime a b) :
-- imply
  jacobiSym (a : ℤ) b =
    (-1 : ℤ) ^ ∑ i ∈ Finset.Icc 1 ((b - 1) / 2), (i * a) / b := by
-- proof
  apply MetaMathlibExt.eisenstein_lemma_jacobi_symbol_general a b ha_odd hb_odd hab

/--
[eisenstein_lemma_jacobi_symbol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LegendreSymbol/EisensteinJacobiSymbol.lean)
-/
@[path]
private lemma eisenstein_lemma_jacobi_symbol_eq
  {a b : ℕ}
-- given
  (ha_pos : 0 < a)
  (hb_pos : 0 < b)
  (ha_odd : Odd a)
  (hb_odd : Odd b)
  (hab : Nat.Coprime a b) :
-- imply
  jacobiSym (a : ℤ) b =
    (-1 : ℤ) ^ ∑ i ∈ Finset.Icc 1 ((b - 1) / 2), (i * a) / b := by
-- proof
  apply MetaMathlibExt.eisenstein_lemma_jacobi_symbol a b ha_pos hb_pos ha_odd hb_odd hab


-- created on 2026-10-20
