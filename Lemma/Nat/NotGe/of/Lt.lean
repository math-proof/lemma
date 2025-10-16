import Lemma.Nat.Lt.is.Le.NotGe
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  ¬a ≥ b := by
-- proof
  let ⟨_, h⟩ := Le.NotGe.of.Lt h
  intro h
  contradiction


-- created on 2025-03-21
-- updated on 2025-08-02
