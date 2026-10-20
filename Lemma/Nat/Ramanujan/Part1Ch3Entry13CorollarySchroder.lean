import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry13CorollarySchroder
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry13CorollarySchroder


/--
[schroder_abel_binomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry13CorollarySchroder.lean)
-/
@[path]
private lemma schroder_abel_binomial_eq
  {w x y : ℂ}
  {n : ℕ} :
-- imply
  (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) *
    (if j = 0 then 1 else x * (x + (j : ℂ) * w) ^ (j - 1)) *
    (if n - j = 0 then 1
    else y * (y + ((n - j : ℕ) : ℂ) * w) ^ (n - j - 1))) =
    if n = 0 then 1 else (x + y) * (x + y + (n : ℂ) * w) ^ (n - 1) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry13CorollarySchroder.schroder_abel_binomial w x y n

/--
[ramanujan_part1_ch3_entry13_corollary_schroder](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry13CorollarySchroder.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry13_corollary_schroder_eq
  {z w : ℂ}
-- given
  (hw : ‖w‖ ≤ ‖Complex.exp (w - 1)‖)
  (hw1 : ‖w‖ ≤ 1) :
-- imply
  HasSum (fun k : ℕ => if k = 0 then 1 else z * (z + (k : ℂ) * w) ^ (k - 1) *
    Complex.exp (-(k : ℂ) * w) / (Nat.factorial k : ℂ)) (Complex.exp z) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry13CorollarySchroder.ramanujan_part1_ch3_entry13_corollary_schroder z w hw hw1


-- created on 2026-10-20
