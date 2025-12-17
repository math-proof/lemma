import Lemma.Int.AbsMul.eq.MulAbsS
import Lemma.Hyperreal.EqSquareSqrt.of.Gt_0
import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Nat.Square.eq.Mul
import Lemma.Nat.LeMulS.of.Le.Le.Ge_0.Ge_0
import Lemma.Real.GtSqrt_0.of.Gt_0
open Nat Real Hyperreal Int


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinite a)
  (h_b : ¬Infinite b) :
-- imply
  ¬Infinite (a * b) := by
-- proof
  apply NotInfinite.of.Any_LeAbs
  let ⟨⟨δ_a, hδ_a⟩, h_a⟩ := Any_LeAbs.of.NotInfinite h_a
  let ⟨⟨δ_b, hδ_b⟩, h_b⟩ := Any_LeAbs.of.NotInfinite h_b
  use ⟨δ_a * δ_b, by simp_all⟩
  calc
    _ = _ := Int.AbsMul.eq.MulAbsS a b
    _ ≤ _ := by
      simp
      apply LeMulS.of.Le.Le.Ge_0.Ge_0
      .
        simp
        linarith
      .
        simp
      .
        simp_all
      .
        simp_all


-- created on 2025-12-17
