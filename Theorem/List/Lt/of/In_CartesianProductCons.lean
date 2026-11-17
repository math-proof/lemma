module

public import Theorem.Set.All_LtGetS.of.In_CartesianProduct

public section

open Set


public theorem List.Lt.of.In_CartesianProductCons
  {x₀ s₀ : ℕ}
  {x s : List ℕ}
-- given
  (h : (x₀ :: x) ∈ (s₀ :: s).cartesianProduct) :
-- imply
  x₀ < s₀ := by
-- proof
  have h := All_LtGetS.of.In_CartesianProduct h
  specialize h 0
  simp at h
  assumption


-- created on 2025-06-14
