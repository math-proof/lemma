import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry.Part3

open Ramanujan.Part1Ch5.Entry10bEuleriansymmetry

/--
[Part1Ch5Entry10bEuleriansymmetry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry10bEuleriansymmetry.lean)
-/
@[path]
private lemma chapter5_euler_even_zero_eq :
-- imply
  chapter5EulerEven 0 = 1 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.chapter5EulerEven_zero

/--
[Part1Ch5Entry10bEuleriansymmetry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry10bEuleriansymmetry.lean)
-/
@[path]
private lemma chapter5_euler_even_step_eq
-- given
  (m : ℕ)
  (hm : m ≠ 0) :
-- imply
  chapter5EulerEven m =
    -∑ k : Fin m, (Nat.choose (2 * m) (2 * k.val) : ℤ) * chapter5EulerEven k.val := by
-- proof
  apply Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.chapter5EulerEven_step m hm

/--
[Part1Ch5Entry10bEuleriansymmetry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry10bEuleriansymmetry.lean)
-/
@[path]
private lemma chapter5_euler_even_recurrence_eq
-- given
  (m : ℕ) :
-- imply
  ∑ k ∈ Finset.range (m + 1), ((Nat.choose (2 * m) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k =
    if m = 0 then 1 else 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.chapter5EulerEven_recurrence m

/--
[Part1Ch5Entry10bEuleriansymmetry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry10bEuleriansymmetry.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry10b_eulerian_symmetry_eq
-- given
  (n : ℕ) :
-- imply
  (2 : ℚ) ^ (2 * n) * ((2 : ℚ) ^ (2 * n) - 1) * bernoulli (2 * n) =
    ((2 * n : ℕ) : ℚ) *
      ∑ k ∈ Finset.range n,
        (Nat.choose (2 * n - 2) (2 * k) : ℚ) *
          (chapter5EulerEven k : ℚ) *
            (chapter5EulerEven (n - k - 1) : ℚ) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.ramanujan_part1_ch5_entry10b_euleriansymmetry n

-- created on 2026-10-10
