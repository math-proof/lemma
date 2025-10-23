import Lemma.Complex.Norm.eq.SqrtAddSqaureS
import Lemma.Algebra.EqSqrt_0.is.Le_0
import Lemma.Int.AddSquareS.ge.Zero
import Lemma.Nat.Eq.of.Ge.Le
import Lemma.Algebra.Eq.of.EqReS.EqImS
import Lemma.Int.Eq_0.and.Eq_0.of.AddSquareS.eq.Zero
open Algebra Nat Complex Int


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : ‖z‖ = 0) :
-- imply
  z = 0 := by
-- proof
  have := Norm.eq.SqrtAddSqaureS (z := z)
  rw [h] at this
  have h_Le_0 := Le_0.of.EqSqrt_0 this.symm
  have h_Ge_0 := AddSquareS.ge.Zero (a := re z) (b := im z)
  have := Eq.of.Ge.Le h_Ge_0 h_Le_0
  have ⟨left, right⟩ := Eq_0.and.Eq_0.of.AddSquareS.eq.Zero this
  apply Eq.of.EqReS.EqImS <;>
  ·
    simp
    assumption


-- created on 2025-01-16
-- updated on 2025-01-26
