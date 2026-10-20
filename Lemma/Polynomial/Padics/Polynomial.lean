import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.Polynomial
open Polynomial


/--
[padicValuation_le_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
private lemma padicValuation_le_coeff_eq
  {p : ℕ}
  {hp : Nat.Prime p}
  {f : Polynomial ℤ}
  {hf : f ≠ 0}
  {n : ℕ}
-- given
  (hn : n ∈ f.support) :
-- imply
  padicValuation p hp f hf ≤ padicValInt p (f.coeff n) := by
-- proof
  apply Polynomial.padicValuation_le_coeff hn

/--
[le_padicValuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
private lemma le_padicValuation_eq
  {p : ℕ}
  {hp : Nat.Prime p}
  {f : Polynomial ℤ}
  {hf : f ≠ 0}
  {k : ℕ}
-- given
  (hk : ∀ n ∈ f.support, k ≤ padicValInt p (f.coeff n)) :
-- imply
  k ≤ padicValuation p hp f hf := by
-- proof
  apply Polynomial.le_padicValuation hk

/--
[padicValuation_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
private lemma padicValuation_C_eq
  {p : ℕ}
  {a : ℤ}
-- given
  (hp : Nat.Prime p)
  (ha : a ≠ 0) :
-- imply
  padicValuation p hp (C a) (C_ne_zero.mpr ha) = padicValInt p a := by
-- proof
  apply Polynomial.padicValuation_C p hp a ha


-- created on 2026-10-20
