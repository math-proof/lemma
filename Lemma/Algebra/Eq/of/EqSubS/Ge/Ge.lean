import Lemma.Algebra.EqSubAdd
import Lemma.Nat.EqAddSub.of.Ge
open Algebra Nat


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : x ≥ d)
  (h₁ : y ≥ d)
  (h₂ : x - d = y - d) :
-- imply
  x = y := by
-- proof
  let y' := y - d
  have h_y : y = y' + d := by 
    simp [y', h₁]
  rw [h_y] at h₂ ⊢
  rw [EqSubAdd.int] at h₂
  rw [← h₂]
  rw [EqAddSub.of.Ge h₀]


-- created on 2025-06-21
