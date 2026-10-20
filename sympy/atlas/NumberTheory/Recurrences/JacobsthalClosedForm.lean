/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/JacobsthalClosedForm.lean -/

import Mathlib.Data.Rat.Init
import sympy.atlas.NumberTheory.BinetClosedForm
namespace MetaMathlibExt

/--
The closed form for the Jacobsthal sequence with initial values
`J 0 = 1` and `J 1 = 1`.

Source: Darrin D. Frey and James A. Sellers, "Jacobsthal Numbers and
Alternating Sign Matrices," Journal of Integer Sequences 3 (2000),
Article 00.2.3, recurrence (label jacrecur) with initial values,
lines 260–266, and Theorem, equation (Eq4a), lines 329–335,
https://cs.uwaterloo.ca/journals/JIS/VOL3/SELLERS/sellers.tex

The explicit formula is the source's Theorem; the source cites
A. Tucker, "Applied Combinatorics," 3rd edition.
It follows from `binet_closed_form_second_order` with `P = 1`, `Q = -2`,
`α = 2` and `β = -1`.
Proves `Wanted` entry `jacobsthal_closedForm`.
-/
theorem jacobsthal_closedForm
    (J : ℕ → ℕ)
    (h_zero : J 0 = 1)
    (h_one : J 1 = 1)
    (h_rec : ∀ n : ℕ, J (n + 2) = J (n + 1) + 2 * J n)
    (m : ℕ) :
    (J m : ℚ) = ((2 : ℚ) ^ (m + 1) + (-1 : ℚ) ^ m) / 3 := by
  have h := binet_closed_form_second_order (fun n => (J n : ℚ)) 1 (-2) 2 (-1)
    (by norm_num) (by norm_num) (by norm_num) (fun n => by simp [h_rec n]) m
  simp only [h_zero, h_one] at h
  rw [h, pow_succ]
  ring

end MetaMathlibExt
