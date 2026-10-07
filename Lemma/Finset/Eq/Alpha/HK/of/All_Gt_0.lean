import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0
open Finset Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ j, 1 ≤ j → j < n → x j > 0) :
-- imply
  alpha ((List.range n).map x) = H x n / K x n := by
-- proof
  exact Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x h₀ h


@[main]
private lemma induct
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≥ 2)
  (h : ∀ j, 1 ≤ j → j < n + 1 → x j > 0) :
-- imply
  alpha ((List.range n).map x) = H x n / K x n := by
-- proof
  exact Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x (by omega) (fun j h1 h2 => h j h1 (by omega))


@[main]
private lemma offset0
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, x i > 0) :
-- imply
  alpha ((List.range n).map x) = H x n / K x n := by
-- proof
  exact Alpha_MapRange.eq.DivHK.of.All_Imp_Gt_0.Gt_0 x h₀ (fun j _ h2 => h j h2)


-- created on 2020-09-24
