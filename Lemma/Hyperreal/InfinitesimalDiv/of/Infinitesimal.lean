import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Int.GtAbs_0.of.Ne_0
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.LtDiv.is.Lt_Mul.of.Gt_0
open Hyperreal Int Rat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinitesimal x)
  (r : ℝ) :
-- imply
  Infinitesimal (x / r) := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  have h := All_LtAbs.of.Infinitesimal h
  simp at ⊢ h
  if h_r : r = 0 then
    subst h_r
    simpa
  else
    have h_r := GtAbs_0.of.Ne_0 h_r
    have h := h (|r| * δ) (by nlinarith)
    simp at h
    rw [AbsDiv.eq.DivAbsS]
    apply LtDiv.of.Lt_Mul.Gt_0 _ h
    simpa


-- created on 2025-12-11
