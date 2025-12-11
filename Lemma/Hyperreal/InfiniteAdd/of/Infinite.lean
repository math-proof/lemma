import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Int.GeAbs_0
import Lemma.Int.SubAbsS.le.AbsAdd
import Lemma.Nat.Gt.of.Ge.Gt
open Hyperreal Int Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinite x)
  (r : ℝ) :
-- imply
  Infinite (x + r) := by
-- proof
  apply Infinite.of.All_GtAbs
  have h := All_GtAbs.of.Infinite h
  intro ⟨δ, hδ⟩
  have h_r := GeAbs_0 r
  have h := h ⟨|r| + δ, by linarith⟩
  simp at ⊢ h
  have h_ge := SubAbsS.le.AbsAdd x r
  apply Gt.of.Ge.Gt h_ge
  linarith


-- created on 2025-12-11
