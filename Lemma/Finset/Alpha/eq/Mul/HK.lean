import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Gt_0
open Finset Continuant


@[path]
private lemma induct
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (_h₀ : n ≥ 2)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range (n + 1)).map x) = H x (n + 1) / K x (n + 1) := by
-- proof
  exact Alpha_MapRange.eq.DivHK.of.All_Gt_0 x h n


-- created on 2020-09-19
