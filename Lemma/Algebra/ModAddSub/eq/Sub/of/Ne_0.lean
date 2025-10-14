import Lemma.Nat.EqSubAdd
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Algebra.EqAddSub.of.Gt
import Lemma.Algebra.EqMod.of.Lt
import Lemma.Algebra.LtSub.of.Lt
open Algebra Nat


@[main]
private lemma main
  {j n : ℕ}
-- given
  (h₀ : i ≥ j)
  (h₁ : i < n)
  (h₂ : j < n) :
-- imply
  (n - j + i) % n = i - j := by
-- proof
  let d := i - j
  have h_eq : i = d + j := by
    simp [d, h₀]
  rw [h_eq]
  rw [EqSubAdd]
  rw [Add.comm (b := j)]
  rw [Add_Add.eq.AddAdd]
  rw [EqAddSub.of.Gt h₂]
  simp
  rw [EqMod.of.Lt]
  simp [d]
  apply LtSub.of.Lt h₁


-- created on 2025-06-21
