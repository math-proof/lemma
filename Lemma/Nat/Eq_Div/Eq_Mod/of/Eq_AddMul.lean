import Lemma.Nat.Eq_Div.of.Eq_AddMul
import Lemma.Nat.Eq_Mod.of.Eq_AddMul
open Nat


@[main]
private lemma main
  {k n m : ℕ}
  {i : Fin m}
  {j : Fin n}
-- given
  (h : k = i * n + j) :
-- imply
  i = k / n ∧ j = k % n := by
-- proof
  constructor
  ·
    apply Eq_Div.of.Eq_AddMul h
  ·
    apply Eq_Mod.of.Eq_AddMul h


-- created on 2025-07-06
-- updated on 2025-07-07
