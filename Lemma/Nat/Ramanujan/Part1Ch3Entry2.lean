import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry2
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry2
open Entry2Leftsummable


/--
[ramanujan_part1_ch3_entry2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_eq
  {x z : ℂ}
-- given
  (hz : ∀ r : ℕ, (z + (r : ℂ)) ≠ 0) :
-- imply
  HasSum (fun j : ℕ => x ^ (j + 1) / ((z + (j : ℂ)) * (Nat.factorial j : ℂ)))
    (Complex.exp x * ∑' (j : ℕ),
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1), (z + (k : ℂ)))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2.ramanujan_part1_ch3_entry2 x z hz

/--
[ramanujan_part1_ch3_entry2_leftsummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_leftsummable_eq
  {x z : ℂ}
-- given
  (hz : ∀ r : ℕ, z + (r : ℂ) ≠ 0) :
-- imply
  Summable (fun j : ℕ => x ^ (j + 1) / ((z + (j : ℂ)) * (Nat.factorial j : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Leftsummable.ramanujan_part1_ch3_entry2_leftsummable x z hz


-- created on 2026-10-20
