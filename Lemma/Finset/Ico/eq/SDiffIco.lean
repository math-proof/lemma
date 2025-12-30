import Lemma.Bool.Ne.is.NotEq
import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Finset.Le.of.In_Ico
import Lemma.Finset.Lt.of.In_Ico
import Lemma.Finset.NotIn.of.In_SDiff
import Lemma.Finset.In.of.In_SDiff
import Lemma.Finset.In_SDiff.is.In.NotIn
import Lemma.Finset.In_Ico.is.Le.Lt
open Nat Bool Finset


@[main]
private lemma main
-- given
  (i n : ℕ) :
-- imply
  Finset.Ico (i + 1) n = Finset.Ico i n \ {i} := by
-- proof
  apply Finset.ext
  intro t
  constructor
  ·
    intro h_t
    have h_i := Le.of.In_Ico h_t
    apply In_SDiff.of.In.NotIn
    ·
      apply In_Ico.of.Le.Lt
      ·
        apply Ge.of.Ge.Ge h_i
        simp
      ·
        apply Lt.of.In_Ico h_t
    ·
      simp
      linarith
  ·
    intro h_t
    have h_in := In.of.In_SDiff h_t
    apply In_Ico.of.Le.Lt
    .
      apply LeAdd_1.of.Lt
      have h_i := Le.of.In_Ico h_in
      apply Lt.of.Le.Ne h_i
      symm
      have h_ne := NotIn.of.In_SDiff h_t
      simp at h_ne
      apply Ne.of.NotEq h_ne
    .
      apply Lt.of.In_Ico h_in


-- created on 2025-12-16
