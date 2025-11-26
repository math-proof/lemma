import Lemma.List.Slice.eq.Nil.of.Ge
import Lemma.Nat.Gt.of.Ge.Gt
import Lemma.List.EqAppendTake__Drop
import Lemma.Bool.EqUFnS.of.Eq
import Lemma.List.DropAppend.eq.AppendDrop.of.GeLength
import Lemma.Nat.Le.of.Le.Lt
import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.Nat.Ge.of.Gt.Ge
import Lemma.List.EqTake.of.Ge_Length
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.Nat.LeSubS.of.Le
import Lemma.List.DropTake.eq.TakeDrop
open List Bool Nat


@[main]
private lemma main
-- given
  (h : j' ≥ j)
  (s : List α) :
-- imply
  (s.take j').slice i j = s.slice i j := by
-- proof
  if h_and : i < j ∧ j ≤ s.length then
    let ⟨h_ij, h_j⟩ := h_and
    have h_i := Le.of.Le.Lt h_ij h_j
    unfold List.slice List.array_slice Function.comp
    have h_j' := Gt.of.Ge.Gt h h_ij
    have := EqAppendTake__Drop s j'
    have := EqUFnS.of.Eq this (fun s => s.drop i)
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
      rw [EqTake.of.Ge_Length h_j]


-- created on 2025-06-20
