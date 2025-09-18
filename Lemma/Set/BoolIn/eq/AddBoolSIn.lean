import Lemma.Set.In.is.In_Inter.ou.In_SDiff
import Lemma.Logic.EqBoolS.of.Iff
import Lemma.Logic.BoolOr.eq.SubAddBoolS
import Lemma.Set.In_Inter.is.In.In
import Lemma.Set.InterInter.eq.Inter_Inter
open Set Logic


@[main, comm]
private lemma fin
  [DecidableEq α]
  {A B : Finset α}
  {x : α} :
-- imply
  Bool.toNat (x ∈ A) = Bool.toNat (x ∈ A ∩ B) + Bool.toNat (x ∈ A \ B) := by
-- proof
  have := In.is.In_Inter.ou.In_SDiff.fin (x := x) (A := A) (B := B)
  have := EqBoolS.of.Iff this
  rw [BoolOr.eq.SubAddBoolS] at this
  rw [this]
  suffices h : Bool.toNat (x ∈ A ∩ B ∧ x ∈ A \ B) = 0 by
    rw [h]
    simp
  simp only [In.In.is.In_Inter.fin]
  simp


@[main, comm]
private lemma main
  [DecidableRel (· ∈ · : α → Set α → Prop)]
  {A B : Set α}
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
  simp only [In.In.is.In_Inter]
  simp only [InterInter.eq.Inter_Inter]
  simp


-- created on 2025-05-01
