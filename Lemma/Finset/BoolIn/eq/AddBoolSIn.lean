import Lemma.Bool.BoolOr.eq.SubAddBoolS
import Lemma.Bool.EqBoolS.of.Iff
import Lemma.Finset.In.is.In_Inter.ou.In_SDiff
import Lemma.Finset.In_Inter.is.In.In
open Bool Finset


@[main, comm]
private lemma main
  [DecidableEq α]
  {A B : Finset α}
  {x : α} :
-- imply
  Bool.toNat (x ∈ A) = Bool.toNat (x ∈ A ∩ B) + Bool.toNat (x ∈ A \ B) := by
-- proof
  have := In.is.In_Inter.ou.In_SDiff (x := x) (A := A) (B := B)
  have := EqBoolS.of.Iff this
  rw [BoolOr.eq.SubAddBoolS] at this
  rw [this]
  suffices h : Bool.toNat (x ∈ A ∩ B ∧ x ∈ A \ B) = 0 by
    rw [h]
    simp
  simp only [In.In.is.In_Inter (e := x)]
  simp


-- created on 2025-12-30
