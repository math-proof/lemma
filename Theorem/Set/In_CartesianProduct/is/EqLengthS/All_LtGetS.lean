module

public import Theorem.List.Any_Eq_GetCartesianProduct.of.All_LtGetS.Length
public import Theorem.List.Length.of.In_CartesianProduct
public import Theorem.Set.All_LtGetS.of.In_CartesianProduct

public section

open Set List


@[comm, mp, mpr]
public theorem Set.In_CartesianProduct.is.EqLengthS.All_LtGetS
-- given
  (x s : List ℕ) :
-- imply
  x ∈ s.cartesianProduct ↔ x.length = s.length ∧ ∀ i (h_x : i < x.length) (h_s : i < s.length), x[i] < s[i] := by
-- proof
  constructor
  ·
    intro h
    constructor
    ·
      apply Length.of.In_CartesianProduct h
    ·
      apply All_LtGetS.of.In_CartesianProduct h
  ·
    intro ⟨h_eq, h_all⟩
    apply In.of.Any_Eq_Get
    apply Any_Eq_GetCartesianProduct.of.All_LtGetS.Length h_eq h_all


-- created on 2025-06-14
