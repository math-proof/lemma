import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry3Psisummable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry3Psisummable


/--
[ramanujan_part1_ch3_entry3_psisummable_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3Psisummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry3_psisummable_general_eq
  {x : ℂ}
  {ε : ℝ}
-- given
  (hε₁ : 0 < ε) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
    Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
    (z + (↑(k + 1) : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3Psisummable.ramanujan_part1_ch3_entry3_psisummable_general x ε hε₁

/--
[ramanujan_part1_ch3_entry3_psisummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3Psisummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry3_psisummable_eq
  {x : ℂ}
  {ε : ℝ}
-- given
  (hx : x ≠ 0)
  (hε₁ : 0 < ε)
  (hε₂ : ε < Real.pi) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
    Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
    (z + (↑(k + 1) : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3Psisummable.ramanujan_part1_ch3_entry3_psisummable x hx ε hε₁ hε₂


-- created on 2026-10-20
