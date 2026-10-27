import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLocalLemma
open Finset Fintype


namespace RamseyLocalLemma

/--
[lll_hyp_convert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyLLL.lean)
-/
@[path]
lemma lll_hyp_convert
  {k n : ℕ}
-- given
  (h : ((Nat.choose k 2 * Nat.choose n (k - 2) + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((1 : ℝ) - (Nat.choose k 2 : ℝ)) < 1 / Real.exp 1) :
-- imply
  Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) - (Nat.choose k 2 : ℝ)) * ((Nat.choose k 2 : ℝ) * (Nat.choose n (k - 2) : ℝ) + 1) < 1 := by
-- proof
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : (↑(k.choose 2 * n.choose (k - 2) + 1) : ℝ) *
    (2 : ℝ) ^ ((1 : ℝ) - ↑(k.choose 2)) * Real.exp 1 < 1 := by
    rwa [lt_div_iff₀ hexp] at h
  linarith [show Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) - ↑(k.choose 2)) *
    (↑(k.choose 2) * ↑(n.choose (k - 2)) + 1) =
    (↑(k.choose 2 * n.choose (k - 2) + 1) : ℝ) *
      (2 : ℝ) ^ ((1 : ℝ) - ↑(k.choose 2)) * Real.exp 1 from by push_cast; ring]

end RamseyLocalLemma

namespace RamseyLocalLemma

/--
[spencer_ramsey_lll](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyLLL.lean)
-/
@[path]
lemma spencer_ramsey_lll
  {k n : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkn : k ≤ n)
  (h : ((Nat.choose k 2 * Nat.choose n (k - 2) + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((1 : ℝ) - (Nat.choose k 2 : ℝ)) < 1 / Real.exp 1) :
-- imply
  ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
-- proof
  spencer_ramsey_lower_bound n k hk hkn (lll_hyp_convert k n h)

end RamseyLocalLemma


-- created on 2026-10-23
