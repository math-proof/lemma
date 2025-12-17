import Lemma.Hyperreal.EqSquareSqrt.of.Gt_0
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Nat.LtMulS.of.Lt.Lt.Gt_0.Gt_0
import Lemma.Nat.Square.eq.Mul
import Lemma.Real.GtSqrt_0.of.Gt_0
import sympy.polys.polyroots
open Hyperreal Nat Real


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : Infinitesimal b) :
-- imply
  Infinitesimal (a * b) := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  simp
  have h_a := All_LtAbs.of.Infinitesimal h_a
  have h_b := All_LtAbs.of.Infinitesimal h_b
  have hδ_sqrt := GtSqrt_0.of.Gt_0 hδ
  have h_a := h_a ⟨√δ, hδ_sqrt⟩
  have h_b := h_b ⟨√δ, hδ_sqrt⟩
  if h_b : b = 0 then
    subst h_b
    simp_all
  else
    calc
      |a| * |b| < √δ * √δ := by
        apply LtMulS.of.Lt.Lt.Gt_0.Gt_0
        repeat simpa
      _ = _ := by
        rw [Mul.eq.Square]
        have := EqSquareSqrt.of.Gt_0 hδ
        simp at this
        conv_rhs => rw [← this]
        rfl


-- created on 2025-12-09
-- updated on 2025-12-10
