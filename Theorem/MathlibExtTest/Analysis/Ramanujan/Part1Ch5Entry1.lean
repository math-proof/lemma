/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch5Entry1.lean -/


import Def.Analysis.Ramanujan.Part1Ch5Entry1
import Lemma.Real.Ramanujan.Part1Ch5Entry1
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 1 API checks

The Bernoulli coefficients and direct uses of both clauses of the exported theorem.
-/


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry1

open Polynomial MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry1
  MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry1Euleriangf

-- The coefficients are the Bernoulli numbers divided by factorials.
example (n : ℕ) : chapter5Entry1MinusCoeff n = (bernoulli n : ℝ) / (n.factorial : ℝ) := rfl

-- The first coefficients are `1`, `-1 / 2` and `1 / 12`.
example : chapter5Entry1MinusCoeff 0 = 1 := by
  simp [chapter5Entry1MinusCoeff]

example : chapter5Entry1MinusCoeff 1 = -1 / 2 := by
  simp [chapter5Entry1MinusCoeff, bernoulli_one]

example : chapter5Entry1MinusCoeff 2 = 1 / 12 := by
  rw [chapter5Entry1MinusCoeff, bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_two]
  norm_num [Nat.factorial]

-- The Bernoulli coefficients satisfy the shift-derivative identity; for `X` the right side is `h`.
example (phi : ℝ[X]) (h : ℝ) :
    taylor h (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi) -
        chapter5DerivativeExpansion chapter5Entry1MinusCoeff h phi =
      C h * derivative phi :=
  ramanujan_part1_ch5_entry1.1 phi h

example (h : ℝ) :
    taylor h (chapter5DerivativeExpansion chapter5Entry1MinusCoeff h X) -
        chapter5DerivativeExpansion chapter5Entry1MinusCoeff h X = C h := by
  simpa using ramanujan_part1_ch5_entry1.1 X h

-- Any coefficient sequence satisfying the identity starts with `-1 / 2` at index `1`.
example (a : ℕ → ℝ)
    (ha : ∀ (phi : ℝ[X]) (h : ℝ),
      taylor h (chapter5DerivativeExpansion a h phi) - chapter5DerivativeExpansion a h phi =
        C h * derivative phi) :
    a 1 = -1 / 2 := by
  rw [ramanujan_part1_ch5_entry1.2 a ha]
  simp [chapter5Entry1MinusCoeff, bernoulli_one]

end MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry1
