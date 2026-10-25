/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PolynomialTL1.lean -/


import Def.NumberTheory.PolynomialTL1
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt


namespace MetaMathlibExt

open Polynomial

example (S : ℕ → Polynomial ℝ) (l : ℕ) (x : ℝ) :
    TIntegrand S l x =
      (8 * x ^ l - Polynomial.aeval x (S l)) / (Real.sqrt x * (4 - x)) := rfl

example (S T : ℕ → Polynomial ℝ) (hzero : T 0 = 0)
    (hdegree : ∀ l : ℕ, 1 ≤ l → (T l).natDegree = l - 1 ∧ T l ≠ 0)
    (hderiv : ∀ l : ℕ, 1 ≤ l → ∀ x : ℝ, 0 < x → x < 4 →
      HasDerivAt (fun y : ℝ => 2 * Real.sqrt y * Polynomial.aeval y (T l))
        (TIntegrand S l x) x) : IsPolyTFamily S T :=
  ⟨hzero, hdegree, hderiv⟩

example {S T : ℕ → Polynomial ℝ} (h : IsPolyTFamily S T) : T 0 = 0 := h.1

example {S T : ℕ → Polynomial ℝ} (h : IsPolyTFamily S T)
    (l : ℕ) (hl : 1 ≤ l) : (T l).natDegree = l - 1 :=
  (h.2.1 l hl).1

example {S T : ℕ → Polynomial ℝ} (h : IsPolyTFamily S T)
    (l : ℕ) (hl : 1 ≤ l) : T l ≠ 0 :=
  (h.2.1 l hl).2


end MetaMathlibExt
