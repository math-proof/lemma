import sympy.concrete.continuant
import sympy.Basic
import Lemma.Finset.All_GeK_0.et.GtK_Add_1_0
open Finset Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ)
  (m : ℕ)
  (hm : 0 < m)
  (h : ∀ i, 1 ≤ i → i < m → 0 < x i) :
-- imply
  0 < K x m := by
-- proof
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact (All_GeK_0.et.GtK_Add_1_0 x k h).2


-- created on 2026-10-07
