import Lemma.Nat.LtMulS.of.Lt.Le.Gt_0.Gt_0
import Lemma.Hyperreal.EqSquareSqrt.of.Gt_0
import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.NotInfinitesimal.is.Any_GeAbs
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Nat.Square.eq.Mul
import Lemma.Rat.Div.gt.Zero.of.Gt_0.Gt_0
open Hyperreal Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : ¬Infinitesimal b) :
-- imply
  Infinite (a * b) := by
-- proof
  apply Infinite.of.All_GtAbs
  intro ⟨δ, hδ⟩
  simp
  have h_a := All_GtAbs.of.Infinite h_a
  let ⟨⟨B, hB⟩, h_b⟩ := Any_GeAbs.of.NotInfinitesimal h_b
  simp at h_b
  have h_div_pos := Div.gt.Zero.of.Gt_0.Gt_0 hδ hB
  have h_a := h_a ⟨δ / B, h_div_pos⟩
  simp at h_a
  calc
    |a| * |b| > δ / B * B := by
      apply GtMulS.of.Gt.Ge.Gt_0.Gt_0
      ·
        apply Gt.of.Gt.Gt h_a
        simp_all
      repeat simp_all
    _ = _ := by
      rw [EqMulDiv.of.Ne_0]
      simp
      linarith


-- created on 2025-12-20
