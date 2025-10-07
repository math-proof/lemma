import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Bool.Ne.is.NotEq
import Lemma.Algebra.LeAdd_1.of.Lt
import Lemma.Algebra.Ge.of.Ge.Ge
import Lemma.Set.Le.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
import Lemma.Set.In_SDiff.is.In.NotIn
import Lemma.Set.In_Ico.of.Le.Lt
import Lemma.Set.NotIn.of.In_SDiff
import Lemma.Set.In.of.In_SDiff
open Algebra Set Bool


@[main]
private lemma main
-- given
  (i n : ℕ) :
-- imply
  Ico (i + 1) n = Ico i n \ {i} := by
-- proof
  apply Set.ext
  intro t
  constructor
  ·
    intro ht
    let ⟨h_i, h_n⟩ := ht
    constructor
    ·
      constructor
      ·
        apply Ge.of.Ge.Ge h_i
        simp
      ·
        assumption
    ·
      simp
      linarith
  ·
    intro ht
    let ⟨⟨h_i, h_n⟩, h_ne⟩ := ht
    simp at h_ne
    have h_ne := Ne.of.NotEq h_ne
    have h_i := Lt.of.Le.Ne h_ne.symm h_i
    constructor
    ·
      apply LeAdd_1.of.Lt h_i
    ·
      assumption


@[main]
private lemma fin
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
    have h_i := Le.of.In_Ico.fin h_t
    have h_n := Lt.of.In_Ico.fin h_t
    apply In_SDiff.of.In.NotIn.fin
    ·
      apply In_Ico.of.Le.Lt.fin
      ·
        apply Ge.of.Ge.Ge h_i
        simp
      ·
        assumption
    ·
      simp
      linarith
  ·
    intro h_t
    have h_ne := NotIn.of.In_SDiff.fin h_t
    have h_in := In.of.In_SDiff.fin h_t
    have h_i := Le.of.In_Ico.fin h_in
    have h_n := Lt.of.In_Ico.fin h_in
    simp at h_ne
    have h_ne := Ne.of.NotEq h_ne
    have h_i := Lt.of.Le.Ne h_ne.symm h_i
    apply In_Ico.of.Le.Lt.fin
    ·
      apply LeAdd_1.of.Lt h_i
    ·
      assumption


-- created on 2025-05-18
