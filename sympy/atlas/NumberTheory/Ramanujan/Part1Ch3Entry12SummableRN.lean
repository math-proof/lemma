/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12SummableRN.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Complex.Exponential
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry12SummableSuccN
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 12

Summability of (n+k)^(r+k)/(aᵏk!) for |a|>e.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry12SummableRN

/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, definition (12.1) and Entry 12,
    printed pp. 66-67 / PDF pp. 76-77.
Proves `Wanted` entry `ramanujan_part1_ch3_entry12_summable_r_n`.
-/
theorem ramanujan_part1_ch3_entry12_summable_r_n (r : ℤ)
    (n a : ℂ)
        (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
            (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
    Summable (fun k : ℕ => ‖(n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (Nat.factorial k : ℂ))‖) := by
  have h := Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general (r - 1) n a
      (ha.imp_right fun h => ⟨h.1, by omega⟩)
  simpa only [sub_add_cancel] using h

end Entry12SummableRN

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
