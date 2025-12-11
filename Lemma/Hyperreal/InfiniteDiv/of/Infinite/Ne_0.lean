import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Int.GtAbs_0.of.Ne_0
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.LtMul.is.Lt_Div.of.Gt_0
open Hyperreal Int Rat


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinite x)
  (h_r : r ≠ 0) :
-- imply
  Infinite (x / r) := by
-- proof
  apply Infinite.of.All_GtAbs
  have h := All_GtAbs.of.Infinite h
  intro ⟨δ, hδ⟩
  have h_r := GtAbs_0.of.Ne_0 h_r
  have h := h ⟨|r| * δ, by nlinarith⟩
  simp at ⊢ h
  rw [AbsDiv.eq.DivAbsS]
  apply Lt_Div.of.LtMul.Gt_0 _ h
  simpa


-- created on 2025-12-11
