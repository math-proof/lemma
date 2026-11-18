module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Nat.Min.eq.IteLe
public import Theorem.Nat.Ite.eq.SubIte
public import Theorem.Nat.LeSubS.is.Le.of.Le
public import Theorem.Nat.NotLe.is.Gt
public import Theorem.Nat.Sub.eq.Zero.of.Lt
public import Theorem.Nat.Gt_Min.of.Gt
public import Theorem.Nat.Min

public section

open Nat


@[comm]
public theorem Nat.SubMin.eq.MinSubS
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


public theorem Nat.MinSubS.eq.SubMin
  (a b d : ℕ) :
  (a - d) ⊓ (b - d) = a ⊓ b - d :=
  (SubMin.eq.MinSubS a b d).symm


-- created on 2025-10-16
