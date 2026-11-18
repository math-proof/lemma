module

public import Initialize.Tactic.Attr.Basic

public import Theorem.List.Any_Eq_GetCartesianProduct.of.All_LtGetS.Length
public import Theorem.List.Length.of.In_CartesianProduct
public import Theorem.Set.All_LtGetS.of.In_CartesianProduct
public import Theorem.Set.In.is.Any_Eq_Get

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


public theorem Set.EqLengthS.All_LtGetS.of.In_CartesianProduct
  {x s : List ℕ}
  (h : x ∈ s.cartesianProduct) :
  x.length = s.length ∧ ∀ i (h_x : i < x.length) (h_s : i < s.length), x[i] < s[i] :=
  (Set.In_CartesianProduct.is.EqLengthS.All_LtGetS x s).mp h

public theorem Set.In_CartesianProduct.of.EqLengthS.All_LtGetS
  {x s : List ℕ}
  (h_eq : x.length = s.length)
  (h_all : ∀ i (h_x : i < x.length) (h_s : i < s.length), x[i] < s[i]) :
  x ∈ s.cartesianProduct :=
  (Set.In_CartesianProduct.is.EqLengthS.All_LtGetS x s).mpr ⟨h_eq, h_all⟩

-- created on 2025-06-14
