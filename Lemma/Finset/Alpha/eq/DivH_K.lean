import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Gt_0
open Finset Continuant


@[main]
private lemma positive
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range n).map x) = H x n / K x n := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Alpha_MapRange.eq.DivHK.of.All_Gt_0 x h m


-- created on 2020-09-20
