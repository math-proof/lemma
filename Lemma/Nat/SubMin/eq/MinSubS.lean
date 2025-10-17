import Lemma.Algebra.Min.eq.IteLe
import Lemma.Algebra.Ite.eq.SubIte
import Lemma.Algebra.LeSubS.is.Le.of.Le
import Lemma.Nat.NotLe.is.Gt
import Lemma.Nat.Sub.eq.Zero.of.Lt
import Lemma.Algebra.Gt_Min.of.Gt
import Lemma.Algebra.Min
open Algebra Nat


@[main, comm]
private lemma main
-- given
  (a b d : ℕ) :
-- imply
  a ⊓ b - d = (a - d) ⊓ (b - d) := by
-- proof
  by_cases h : d ≤ b
  · 
    repeat rw [Min.eq.IteLe]
    rw [SubIte.eq.Ite]
    simp [LeSubS.is.Le.of.Le h]
  · 
    have h := Gt.of.NotLe h
    have h_eq := Sub.eq.Zero.of.Lt h
    rw [h_eq]
    simp
    have h := Gt_Min.of.Gt h a
    rw [Min.comm] at h
    have h := Sub.eq.Zero.of.Lt h
    rw [h]


-- created on 2025-10-16
