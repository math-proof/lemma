/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Bernoulli/KummerCongruence.lean -/


import sympy.atlas.NumberTheory.Bernoulli.KummerCongruence
import Lemma.Nat.Bernoulli.KummerCongruence
import Mathlib.Tactic.NormNum

namespace MetaMathlibExtTest

-- Apply Kummer's congruence directly from its local hypotheses.
example {p m n t : ℕ} [Fact (Nat.Prime p)]
    (hm : ¬(p - 1) ∣ m) (hn : ¬(p - 1) ∣ n)
    (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
    ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / (m : ℚ)) =
      ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / (n : ℚ)) ∨
    (t : ℤ) + 1 ≤ padicValRat p
      (((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / (m : ℚ)) -
        ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / (n : ℚ))) :=
  MetaMathlibExt.kummer_congruence hm hn hcong

-- Exercise the first nontrivial congruent pair for p = 5.
example :
    ((1 - (5 : ℚ) ^ (2 - 1)) * bernoulli 2 / (2 : ℚ)) =
      ((1 - (5 : ℚ) ^ (6 - 1)) * bernoulli 6 / (6 : ℚ)) ∨
    (0 : ℤ) + 1 ≤ padicValRat 5
      (((1 - (5 : ℚ) ^ (2 - 1)) * bernoulli 2 / (2 : ℚ)) -
        ((1 - (5 : ℚ) ^ (6 - 1)) * bernoulli 6 / (6 : ℚ))) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply MetaMathlibExt.kummer_congruence (p := 5) (m := 2) (n := 6) (t := 0)
  · norm_num
  · norm_num
  · norm_num [Nat.ModEq]

end MetaMathlibExtTest
