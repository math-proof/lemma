import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset Fintype


namespace SimpleGraph

/--
[CliqueFree.two_mul_r_mul_card_edgeFinset_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Turan.lean)
-/
@[path]
lemma CliqueFree.two_mul_r_mul_card_edgeFinset_le
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : ℕ}
  {cf : G.CliqueFree (r + 1)} :
-- imply
  2 * r * #G.edgeFinset ≤ (r - 1) * (Fintype.card V) ^ 2 := by
-- proof
  calc 2 * r * #G.edgeFinset
    ≤ 2 * r * ((Fintype.card V ^ 2 - (Fintype.card V % r) ^ 2) * (r - 1) / (2 * r) +
      (Fintype.card V % r).choose 2) := by
      gcongr
      exact cf.card_edgeFinset_le
    _ ≤ 2 * r * #(turanGraph (Fintype.card V) r).edgeFinset := by
      gcongr
      rw [card_edgeFinset_turanGraph]
    _ ≤ (r - 1) * (Fintype.card V) ^ 2 :=
      mul_card_edgeFinset_turanGraph_le

end SimpleGraph

namespace SimpleGraph

/--
[CliqueFree.card_edgeFinset_le_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Turan.lean)
-/
@[path]
lemma CliqueFree.card_edgeFinset_le_real
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : ℕ}
  {cf : G.CliqueFree (r + 1)}
-- given
  (hr : 0 < r) :
-- imply
  (#G.edgeFinset : ℝ) ≤ (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by
-- proof
  have hr' : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have h := cf.two_mul_r_mul_card_edgeFinset_le
  have h1 : 1 ≤ r := hr
  have hR : 2 * (r : ℝ) * (↑(#G.edgeFinset)) ≤ ((r : ℝ) - 1) * (↑(Fintype.card V)) ^ 2 := by
    exact_mod_cast h
  have h2r : (0 : ℝ) < 2 * ↑r := mul_pos two_pos hr'
  have hne : (2 * (r : ℝ)) ≠ 0 := ne_of_gt h2r
  calc (↑(#G.edgeFinset) : ℝ)
    = 2 * ↑r * ↑(#G.edgeFinset) / (2 * ↑r) := by
      rw [mul_div_cancel_left₀ _ hne]
    _ ≤ ((↑r - 1) * (↑(Fintype.card V)) ^ 2) / (2 * ↑r) := by
      exact div_le_div_of_nonneg_right hR (le_of_lt h2r)
    _ = (1 - 1 / (↑r : ℝ)) * (↑(Fintype.card V) : ℝ) ^ 2 / 2 := by
      have hne' : (↑r : ℝ) ≠ 0 := ne_of_gt hr'
      have key : (↑r - 1 : ℝ) / (↑r : ℝ) = 1 - 1 / (↑r : ℝ) := by
        rw [sub_div, div_self hne']
      rw [← key, div_mul_eq_mul_div]
      rw [show (2 : ℝ) * (↑r : ℝ) = (↑r : ℝ) * 2 from mul_comm _ _, ← div_div]

end SimpleGraph


-- created on 2026-10-23
