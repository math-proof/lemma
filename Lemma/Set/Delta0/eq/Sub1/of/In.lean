import Lemma.Nat.Delta.eq.Ite
import Lemma.Set.In_Finset.is.OrEqS
open Nat Set


@[main]
private lemma main
-- given
  (h : x ∈ ({0, 1} : Set ℕ)) :
-- imply
  KroneckerDelta (0 : ℕ) x = 1 - x := by
-- proof
  rw [Delta.eq.Ite]
  rcases OrEqS.of.In_Finset h with rfl | rfl <;> simp


-- created on 2020-08-29
-- updated on 2026-09-09
