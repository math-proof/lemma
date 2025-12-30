import Lemma.Finset.In.In.of.In_Inter
import Lemma.Finset.Inter
open Finset


@[main]
private lemma left
  [DecidableEq α]
-- given
  (A B : Finset α) :
-- imply
  A ∩ B ⊆ A := by
-- proof
  intro x hx
  let ⟨hxA, hxB⟩ := In.In.of.In_Inter hx
  assumption


@[main]
private lemma main
  [DecidableEq α]
-- given
  (A B : Finset α) :
-- imply
  A ∩ B ⊆ B := by
-- proof
  have := left B A
  rwa [Inter.comm] at this


-- created on 2025-12-30
