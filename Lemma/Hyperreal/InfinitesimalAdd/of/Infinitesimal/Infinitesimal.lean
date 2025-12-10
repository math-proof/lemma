import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Int.AbsAdd.le.AddAbsS
import Lemma.Nat.LtAddS.of.Lt.Lt
import Lemma.Rat.Div.gt.Zero.of.Gt_0
open Hyperreal Int Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : Infinitesimal b) :
-- imply
  Infinitesimal (a + b) := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  simp
  have h_a := All_LtAbs.of.Infinitesimal h_a
  simp at h_a
  have h_b := All_LtAbs.of.Infinitesimal h_b
  simp at h_b
  have hδ_2 := Div.gt.Zero.of.Gt_0.left hδ (d := 2)
  have h_a := h_a (δ / 2) hδ_2
  have h_b := h_b (δ / 2) hδ_2
  calc _ ≤ _ := AbsAdd.le.AddAbsS (a := a) (b := b)
    _ < δ / 2 + δ / 2 := LtAddS.of.Lt.Lt h_a h_b
    _ = _ := by simp


-- created on 2025-12-09
