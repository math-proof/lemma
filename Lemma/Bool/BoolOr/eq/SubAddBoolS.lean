import Lemma.Bool.Bool.eq.Ite
import Lemma.Nat.AddIteS.eq.IteAnd
import Lemma.Bool.IteOr.eq.Ite__Ite
import Lemma.Nat.SubIteS.eq.IteAnd
import Lemma.Bool.Ite__Ite.eq.Ite
import Lemma.Bool.Or.is.OrAnd
open Bool Nat


@[main]
private lemma main
  [Decidable p]
  [Decidable q] :
-- imply
  Bool.toNat (p ∨ q) = Bool.toNat p + Bool.toNat q - Bool.toNat (p ∧ q) := by
-- proof
  denote h_S : S = Bool.toNat p + Bool.toNat q
  rw [← h_S]
  rw [Bool.eq.Ite, Bool.eq.Ite] at h_S
  rw [AddIteS.eq.IteAnd] at h_S
  simp at h_S
  rw [Ite__Ite.eq.IteOr] at h_S
  rw [h_S]
  rw [Bool.eq.Ite, Bool.eq.Ite]
  rw [SubIteS.eq.IteAnd]
  simp
  simp [Ite__Ite.eq.Ite]
  rw [Ite__Ite.eq.IteOr]
  simp [Or.comm (a := q)]
  simp [← Or.is.OrAnd]


-- created on 2025-04-28
-- updated on 2025-05-01
