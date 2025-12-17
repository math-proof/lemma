import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Int.AbsAdd.le.AddAbsS
import Lemma.Nat.LeAddS.of.Le.Le
open Hyperreal Nat Int


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinite a)
  (h_b : ¬Infinite b) :
-- imply
  ¬Infinite (a + b) := by
-- proof
  apply NotInfinite.of.Any_LeAbs
  let ⟨⟨δ_a, hδ_a⟩, h_a⟩ := Any_LeAbs.of.NotInfinite h_a
  let ⟨⟨δ_b, hδ_b⟩, h_b⟩ := Any_LeAbs.of.NotInfinite h_b
  use ⟨δ_a + δ_b, by linarith⟩
  calc
    _ ≤ _ := AbsAdd.le.AddAbsS a b
    _ ≤ _ := by
      simp
      apply LeAddS.of.Le.Le
      repeat simpa


-- created on 2025-12-17
