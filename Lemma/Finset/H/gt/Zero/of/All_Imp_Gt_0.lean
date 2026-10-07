import sympy.concrete.continuant
import sympy.Basic
import Lemma.Finset.All_GtH_0.et.GtH_Add_1_0
open Finset Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ)
  (m : ℕ)
  (h : ∀ i < m, 0 < x i) :
-- imply
  0 < H x m := by
-- proof
  cases m with
  | zero => simp [H]
  | succ m => exact (All_GtH_0.et.GtH_Add_1_0 x m h).2


-- created on 2026-10-07
