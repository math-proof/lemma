import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.LinkBuilding
import Lemma.Bijective.All_All_All_Any_And_Eq_ImageAndAll_All_Eq_Image.of.All_ChamberAdjacent.All_Any_And_Eq.All_All_Eq.EqToSimplicialComplex
open scoped Classical


/--
[finset_union_left_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkAdjacencyLifting.lean)
-/
@[path]
lemma finset_union_left_cancel
  {V : Type}
  [DecidableEq V]
  {σ C D : Finset V}
-- given
  (hC_disj : Disjoint σ C)
  (hD_disj : Disjoint σ D)
  (h_eq : σ ∪ C = σ ∪ D) :
-- imply
  C = D := by
-- proof
  ext v
  constructor
  · intro hv
    have hv_in : v ∈ σ ∪ D := h_eq ▸ Finset.mem_union_right σ hv
    exact (Finset.mem_union.mp hv_in).elim
      (fun h => absurd h (Finset.disjoint_right.mp hC_disj hv)) id
  · intro hv
    have hv_in : v ∈ σ ∪ C := h_eq.symm ▸ Finset.mem_union_right σ hv
    exact (Finset.mem_union.mp hv_in).elim
      (fun h => absurd h (Finset.disjoint_right.mp hD_disj hv)) id


-- created on 2026-10-24
