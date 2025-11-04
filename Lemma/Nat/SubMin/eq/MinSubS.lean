import Lemma.Nat.Min.eq.IteLe
import Lemma.Nat.Ite.eq.SubIte
import Lemma.Nat.LeSubS.is.Le.of.Le
import Lemma.Nat.NotLe.is.Gt
import Lemma.Nat.Sub.eq.Zero.of.Lt
import Lemma.Nat.Gt_Min.of.Gt
import Lemma.Nat.Min
open Nat


@[main, comm]
private lemma main
-- given
  (a b d : ℕ) :
-- imply
  a ⊓ b - d = (a - d) ⊓ (b - d) := by
-- proof
  if h : d ≤ b then
    repeat rw [Min.eq.IteLe]
    rw [SubIte.eq.Ite]
    simp [LeSubS.is.Le.of.Le h]
  else
    have h := Gt.of.NotLe h
    have h_eq := Sub.eq.Zero.of.Lt h
    rw [h_eq]
    simp
    have h := Gt_Min.of.Gt h a
    rw [Min.comm] at h
    have h := Sub.eq.Zero.of.Lt h
    rw [h]


-- created on 2025-10-16
