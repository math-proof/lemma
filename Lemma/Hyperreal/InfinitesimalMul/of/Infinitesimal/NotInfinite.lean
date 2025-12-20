import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Nat.LtMulS.of.Lt.Le.Gt_0.Gt_0
import Lemma.Rat.Div.gt.Zero.of.Gt_0.Gt_0
import Lemma.Rat.EqMulDiv.of.Ne_0
open Rat Hyperreal Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : ¬Infinite b) :
-- imply
  Infinitesimal (a * b) := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  simp
  have h_a := All_LtAbs.of.Infinitesimal h_a
  let ⟨⟨B, hB⟩, h_b⟩ := Any_LeAbs.of.NotInfinite h_b
  simp at h_b
  have h_div_gt_0 := Div.gt.Zero.of.Gt_0.Gt_0 hδ hB
  have h_a := h_a ⟨δ / B, h_div_gt_0⟩
  if h_b : b = 0 then
    subst h_b
    simp_all
  else
    simp at h_a
    calc
      |a| * |b| < δ / B * B := by
        apply LtMulS.of.Lt.Le.Gt_0.Gt_0
        repeat simp_all
      _ = _ := by
        rw [EqMulDiv.of.Ne_0]
        simp
        linarith


-- created on 2025-12-20
