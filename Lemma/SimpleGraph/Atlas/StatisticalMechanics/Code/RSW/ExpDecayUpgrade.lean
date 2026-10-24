import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.ExpDecayUpgrade
open Real StatMech StatMech.RSW StatMech.RSW.ExpDecay


/--
[rxd_submul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/ExpDecayUpgrade.lean)
-/
@[path]
private lemma rxd_submul_pow_eq
  {a : ℕ → ℝ}
  {n₀ : ℕ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : a 0 ≤ 1)
  (hsub : ∀ m n, a (m + n) ≤ a m * a n) :
-- imply
  ∀ k, a (k * n₀) ≤ (a n₀) ^ k := by
-- proof
  apply StatMech.RSW.ExpDecay.rxd_submul_pow a hnn hle1 hsub n₀

/--
[rxd_submultiplicative_forces_exp_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/ExpDecayUpgrade.lean)
-/
@[path]
private lemma rxd_submultiplicative_forces_exp_decay_eq
  {a : ℕ → ℝ}
  {n₀ : ℕ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : ∀ n, a n ≤ 1)
  (hanti : Antitone a)
  (hsub : ∀ m n, a (m + n) ≤ a m * a n)
  (hn₀ : 0 < n₀)
  (hlt : a n₀ < 1) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, a n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.RSW.ExpDecay.rxd_submultiplicative_forces_exp_decay a hnn hle1 hanti hsub n₀ hn₀ hlt

/--
[rxd_value_lt_one_of_stretched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/ExpDecayUpgrade.lean)
-/
@[path]
private lemma rxd_value_lt_one_of_stretched_eq
  {a : ℕ → ℝ}
  {α : ℝ}
-- given
  (hstr : ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))) :
-- imply
  a 1 < 1 := by
-- proof
  apply StatMech.RSW.ExpDecay.rxd_value_lt_one_of_stretched a α hstr

/--
[rxd_exp_decay_of_stretched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/ExpDecayUpgrade.lean)
-/
@[path]
private lemma rxd_exp_decay_of_stretched_eq
  {a : ℕ → ℝ}
  {α : ℝ}
-- given
  (hnn : ∀ n, 0 ≤ a n)
  (hle1 : ∀ n, a n ≤ 1)
  (hanti : Antitone a)
  (hα : 0 < α)
  (hstr : ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α)))
  (hsub : ∀ m n, a (m + n) ≤ a m * a n) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, a n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.RSW.ExpDecay.rxd_exp_decay_of_stretched a hnn hle1 hanti α hα hstr hsub

/--
[rxd_exp_decay_literal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/ExpDecayUpgrade.lean)
-/
@[path]
private lemma rxd_exp_decay_literal_eq
  {a : ℕ → ℝ}
  {α : ℝ}
-- given
  (hα : 1 ≤ α)
  (hstr : ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))) :
-- imply
  ∃ c > 0, ∀ n, a n ≤ Real.exp (-c * n) := by
-- proof
  apply StatMech.RSW.ExpDecay.rxd_exp_decay_literal a α hα hstr


-- created on 2026-10-23
