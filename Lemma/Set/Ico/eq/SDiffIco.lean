import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Bool.Ne.is.NotEq
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Set.Le.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
import Lemma.Set.In_SDiff.is.In.NotIn
import Lemma.Set.NotIn.of.In_SDiff
import Lemma.Set.In.of.In_SDiff
open Set Bool Nat


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
    have h_i := Lt.of.Le.Ne h_i h_ne.symm
    constructor
    ·
      apply LeAdd_1.of.Lt h_i
    ·
      assumption


-- created on 2025-05-18
