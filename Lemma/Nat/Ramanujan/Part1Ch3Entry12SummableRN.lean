import Mathlib
import sympy.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12SummableRN

/--
[ramanujan_part1_ch3_entry12_summable_r_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12SummableRN.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry12_summable_r_n
  {r : ℤ}
  {n a : ℂ}
-- given
  (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
  (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
-- imply
  Summable (fun k : ℕ => ‖(n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (Nat.factorial k : ℂ))‖) := by
-- proof
  have h := Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general (r - 1) n a
    (ha.imp_right fun h => ⟨h.1, by omega⟩)
  simpa only [sub_add_cancel] using h

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12SummableRN


-- created on 2026-10-20
-- updated on 2026-10-23
