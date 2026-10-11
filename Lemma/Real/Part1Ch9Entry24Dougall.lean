import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry24Dougall

open Ramanujan.Part1Ch9.Entry24Dougall

/--
[Part1Ch9Entry24Dougall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry24Dougall.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry24_dougall_eq
-- given
  (x y theta phi : ℝ)
  (hx : 0 ≤ x ∧ x ≤ 1)
  (hy : 0 ≤ y ∧ y ≤ 1)
  (htheta : -Real.pi < theta ∧ theta ≤ Real.pi)
  (hphi : -Real.pi < phi ∧ phi ≤ Real.pi)
  (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
    (y : ℂ) * Complex.exp (Complex.I * phi) = 1) :
-- imply
  Summable (chapter9DilogCosTerm x theta) ∧
    Summable (chapter9DilogCosTerm y phi) ∧
    Summable (chapter9DilogSinTerm x theta) ∧
    Summable (chapter9DilogSinTerm y phi) ∧
    (∑' j : ℕ, chapter9DilogCosTerm x theta j) +
        ∑' j : ℕ, chapter9DilogCosTerm y phi j =
      Real.pi ^ 2 / 6 - chapter9BoundaryLog x * chapter9BoundaryLog y +
        theta * phi ∧
    (∑' j : ℕ, chapter9DilogSinTerm x theta j) +
        ∑' j : ℕ, chapter9DilogSinTerm y phi j =
      -phi * chapter9BoundaryLog x - theta * chapter9BoundaryLog y := by
-- proof
  apply Ramanujan.Part1Ch9.Entry24Dougall.ramanujan_part1_ch9_entry24_dougall
    x y theta phi hx hy htheta hphi hxy

-- created on 2026-10-10
