import Lemma.Nat.Square.eq.Mul
import Lemma.Nat.LtMulS.of.Lt.Lt.Gt_0.Gt_0
import Lemma.Real.GtSqrt_0.of.Gt_0
import Lemma.Hyperreal.Infinite.is.All_GtAbs
open Hyperreal Real Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : Infinite b) :
-- imply
  Infinite (a * b) := by
-- proof
  apply Infinite.of.All_GtAbs
  intro ⟨δ, hδ⟩
  simp
  have h_a := All_GtAbs.of.Infinite h_a
  have h_b := All_GtAbs.of.Infinite h_b
  have hδ_sqrt := GtSqrt_0.of.Gt_0 hδ
  have h_a := h_a ⟨√δ, hδ_sqrt⟩
  have h_b := h_b ⟨√δ, hδ_sqrt⟩
  calc
    |a| * |b| > √δ * √δ := by
      apply GtMulS.of.Gt.Gt.Gt_0.Gt_0
      .
        apply Gt.of.Gt.Gt h_a
        simpa
      repeat simpa
    _ = _ := by
      rw [Mul.eq.Square]
      have := EqSquareSqrt.of.Gt_0 hδ
      simp at this
      conv_rhs => rw [← this]
      rfl


-- created on 2025-12-16
-- updated on 2025-12-17
