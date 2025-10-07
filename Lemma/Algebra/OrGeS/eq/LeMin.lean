import Lemma.Bool.BFn_Ite.is.OrAndS
import Lemma.Algebra.Min.eq.IteGe
open Algebra Bool


@[main]
private lemma main
  [LinearOrder α]
  {x a b : α}
-- given
  (h : x ≥ a ⊓ b) :
-- imply
  x ≥ a ∨ x ≥ b := by
-- proof
  rw [Min.eq.IteGe] at h
  rw [BFn_Ite.is.OrAndS (R := (· ≥ ·))] at h
  by_cases h_ge : a ≥ b <;>
    simp [h_ge] at h
  ·
    right
    assumption
  ·
    left
    assumption


-- created on 2025-05-14
