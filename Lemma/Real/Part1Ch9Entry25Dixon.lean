import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry25Dixon.Part4

open Ramanujan.Part1Ch9.Entry25Dixon

/--
[Part1Ch9Entry25Dixon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry25Dixon.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry25_dixon_eq
-- given
  (x y theta phi : ℝ)
  (hx : 0 ≤ x ∧ x ≤ 1)
  (hy : 0 ≤ y ∧ y ≤ 1)
  (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
    (y : ℂ) * Complex.exp (Complex.I * phi) =
      (x * y : ℝ) * Complex.exp (Complex.I * (theta + phi))) :
-- imply
  1 - x * Real.cos theta ≠ 0 ∧
    1 - y * Real.cos phi ≠ 0 ∧
    0 < 1 - 2 * x * Real.cos theta + x ^ 2 ∧
    0 < 1 - 2 * y * Real.cos phi + y ^ 2 ∧
    Summable (chapter9DilogCosTerm x theta) ∧
    Summable (chapter9DilogCosTerm y phi) ∧
    Summable (chapter9DilogSinTerm x theta) ∧
    Summable (chapter9DilogSinTerm y phi) ∧
    (∑' j : ℕ, chapter9DilogCosTerm x theta j) +
        ∑' j : ℕ, chapter9DilogCosTerm y phi j =
      Real.log (1 - 2 * x * Real.cos theta + x ^ 2) *
          Real.log (1 - 2 * y * Real.cos phi + y ^ 2) / 8 -
        Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta)) *
          Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi)) / 2 ∧
    (∑' j : ℕ, chapter9DilogSinTerm x theta j) +
        ∑' j : ℕ, chapter9DilogSinTerm y phi j =
      -Real.log (1 - 2 * x * Real.cos theta + x ^ 2) *
          Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi)) / 4 -
        Real.log (1 - 2 * y * Real.cos phi + y ^ 2) *
          Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta)) / 4 := by
-- proof
  apply Ramanujan.Part1Ch9.Entry25Dixon.ramanujan_part1_ch9_entry25_dixon x y theta phi hx hy hxy

-- created on 2026-10-10
