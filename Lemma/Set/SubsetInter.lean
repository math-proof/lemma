import Lemma.Set.Inter
import Lemma.Set.In.In.of.In_Inter
open Set


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  A ∩ B ⊆ B := by
-- proof
  intro x hx
  let ⟨hxA, hxB⟩ := hx
  exact hxB


@[main]
private lemma left
-- given
  (A B : Set α) :
-- imply
  A ∩ B ⊆ A := by
-- proof
  have := main B A
  rw [Inter.comm] at this
  assumption


@[main]
private lemma left.fin
  [DecidableEq α]
-- given
  (A B : Finset α) :
-- imply
  A ∩ B ⊆ A := by
-- proof
  intro x hx
  let ⟨hxA, hxB⟩ := In.In.of.In_Inter.fin hx
  assumption


@[main]
private lemma fin
  [DecidableEq α]
-- given
  (A B : Finset α) :
-- imply
  A ∩ B ⊆ B := by
-- proof
  have := left.fin B A
  rw [Inter.comm.fin] at this
  assumption


-- created on 2025-04-08
-- updated on 2025-08-13
