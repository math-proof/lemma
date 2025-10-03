import Lemma.Set.In.is.Any_Eq_Get
import Lemma.List.Any_Eq_GetCartesianProduct.of.All_LtGetS.EqLengthS
import Lemma.List.EqLengthS.of.In_CartesianProduct
import Lemma.Set.All_LtGetS.of.In_CartesianProduct
open Set List


@[main, comm, mp, mpr]
private lemma main
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
      apply EqLengthS.of.In_CartesianProduct h
    ·
      apply All_LtGetS.of.In_CartesianProduct h
  ·
    intro ⟨h_eq, h_all⟩
    apply In.of.Any_Eq_Get
    apply Any_Eq_GetCartesianProduct.of.All_LtGetS.EqLengthS h_eq h_all


-- created on 2025-06-14
