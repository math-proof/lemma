/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/Polynomial.lean -/


import sympy.atlas.NumberTheory.Padics.Polynomial
import Lemma.Polynomial.Padics.Polynomial

open Polynomial

example :
    Polynomial.padicValuation 2 prime_two (C 12)
      (C_ne_zero.mpr twelve_ne_zero) = 2 := by
  calc
    Polynomial.padicValuation 2 prime_two (C 12) (C_ne_zero.mpr twelve_ne_zero) =
        padicValInt 2 12 := Polynomial.padicValuation_C 2 prime_two 12 twelve_ne_zero
    _ = 2 := padicValInt_two_twelve

example (f : Polynomial ℤ) (hf : f ≠ 0) (n : ℕ) (hn : n ∈ f.support) :
    Polynomial.padicValuation 2 prime_two f hf ≤ padicValInt 2 (f.coeff n) :=
  Polynomial.padicValuation_le_coeff hn

example (f : Polynomial ℤ) (hf : f ≠ 0) (k : ℕ)
    (hk : ∀ n ∈ f.support, k ≤ padicValInt 2 (f.coeff n)) :
    k ≤ Polynomial.padicValuation 2 prime_two f hf :=
  Polynomial.le_padicValuation hk
