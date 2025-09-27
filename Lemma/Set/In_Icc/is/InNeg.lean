import sympy.sets.sets
import Lemma.Algebra.GeNegS.of.Le
import Lemma.Algebra.EqNegNeg
open Algebra


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
-- given
  (x a b : α) :
-- imply
  x ∈ Icc a b ↔ -x ∈ Icc (-b) (-a) := by
-- proof
  constructor <;>
  ·
    intro h
    obtain ⟨h₀, h₁⟩ := h
    have h₀ := GeNegS.of.Le h₀
    have h₁ := GeNegS.of.Le h₁
    repeat rw [EqNegNeg] at h₀ h₁
    exact ⟨h₁, h₀⟩


-- created on 2025-08-02
