import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddBelow (f '' S)) :
-- imply
  sInf (f '' S) = sSup {y | ∀ x ∈ S, f x ≥ y} := by
-- proof
  have e : {y | ∀ x ∈ S, f x ≥ y} = lowerBounds (f '' S) := by
    ext y
    rw [Set.mem_ofPred_eq, mem_lowerBounds, Set.forall_mem_image]
  rw [e]
  exact (IsGreatest.csSup_eq (isGLB_csInf (h₀.image f) h₁)).symm


-- created on 2026-09-27
