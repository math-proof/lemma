import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.K.gt.Zero.of.All_Imp_Gt_0.Gt_0
open Finset Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, 1 ≤ i → i < n → x i > 0) :
-- imply
  K x n > 0 := by
-- proof
  exact K.gt.Zero.of.All_Imp_Gt_0.Gt_0 x n h₀ h


-- created on 2020-09-15
