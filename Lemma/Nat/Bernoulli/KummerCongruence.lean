import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.KummerCongruence
open MetaMathlibExt


/--
[kummer_congruence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/KummerCongruence.lean)
-/
@[path]
private lemma kummer_congruence_eq
  {p m n t : ℕ} [Fact (Nat.Prime p)]
-- given
  (hm_dvd : ¬ (p - 1) ∣ m)
  (hn_dvd : ¬ (p - 1) ∣ n)
  (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
-- imply
  ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / (m : ℚ)) =
    ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / (n : ℚ)) ∨
    (t : ℤ) + 1 ≤ padicValRat p
    (((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / (m : ℚ)) -
    ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / (n : ℚ))) := by
-- proof
  apply MetaMathlibExt.kummer_congruence hm_dvd hn_dvd hcong


-- created on 2026-10-20
