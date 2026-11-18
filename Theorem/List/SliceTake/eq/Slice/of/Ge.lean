module

public import Theorem.List.Slice.eq.Nil.of.Ge
public import Theorem.Nat.Gt.of.Ge.Gt
public import Theorem.List.EqAppendTake__Drop
public import Theorem.Bool.UFn.of.Eq
public import Theorem.List.DropAppend.eq.AppendDrop.of.GeLength
public import Theorem.Bool.NotAnd.is.OrNotS
public import Theorem.Nat.Ge.of.Gt.Ge
public import Theorem.List.EqTake.of.LeLength
public import Theorem.List.TakeTake.eq.Take.of.Ge
public import Theorem.Nat.LeSubS.of.Le
public import Theorem.List.DropTake.eq.TakeDrop

public section

open List Bool Nat


public theorem List.SliceTake.eq.Slice.of.Ge
-- given
  (h : j' ≥ j)
  (s : List α) :
-- imply
  (s.take j').slice i j = s.slice i j := by
-- proof
  if h_and : i < j ∧ j ≤ s.length then
    let ⟨h_ij, h_j⟩ := h_and
    have h_i := le_trans (le_of_lt h_ij) h_j
    unfold List.slice List.array_slice Function.comp
    have h_j' := Gt.of.Ge.Gt h h_ij
    have := EqAppendTake__Drop s j'
    have := UFn.of.Eq this (·.drop i)
    rw [DropAppend.eq.AppendDrop.of.GeLength (by simp_all; linarith)] at this
    rw [DropTake.eq.TakeDrop]
    rw [TakeTake.eq.Take.of.Ge]
    apply GeSubS.of.Ge h
  else
    rw [NotAnd.is.OrNotS] at h_and
    simp at h_and
    obtain h_le | h_lt := h_and
    ·
      simp_all [Slice.eq.Nil.of.Ge h_le]
    ·
      have h_j := Ge.of.Gt.Ge h h_lt
      rw [EqTake.of.LeLength h_j]


-- created on 2025-06-20
