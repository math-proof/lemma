import Lemma.Bool.Bool.eq.Ite
import Lemma.Set.AddIteS.eq.Ite.of.Inter.eq.Empty
open Bool Set


@[main]
private lemma main
  {A B : Set α}
  {x : α}
  [Decidable (x ∈ A)]
  [Decidable (x ∈ B)]
-- given
  (h : A ∩ B = ∅) :
-- imply
  Bool.toNat (x ∈ A ∪ B) = Bool.toNat (x ∈ A) + Bool.toNat (x ∈ B) := by
-- proof
  rw [Bool.eq.Ite, Bool.eq.Ite (p := x ∈ A), Bool.eq.Ite (p := x ∈ B),
    AddIteS.eq.Ite.of.Inter.eq.Empty (A := A) (B := B) (x := x) (a := (1 : ℕ)) (a' := 0) (b := 1)
      (b' := 0) h]
  grind


-- created on 2020-07-04
-- updated on 2026-09-07
