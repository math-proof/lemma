import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part8
open Finset StatMech StatMech.FrontierA


/--
[finiteCutPlusBoundaryField_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutPlusBoundaryField_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (x : {v : V // v ∈ S}) :
-- imply
  0 ≤ finiteCutPlusBoundaryField G S x := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusBoundaryField_nonneg G S x

/--
[abs_finiteCutBoundaryField_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma abs_finiteCutBoundaryField_le_plus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (outside : {v : V // v ∉ S} → Bool)
  (x : {v : V // v ∈ S}) :
-- imply
  |finiteCutBoundaryField G S outside x| ≤ finiteCutPlusBoundaryField G S x := by
-- proof
  apply StatMech.FrontierA.abs_finiteCutBoundaryField_le_plus G S outside x

/--
[finiteCutMerge_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutMerge_inside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool)
  (x : {v : V // v ∈ S}) :
-- imply
  finiteCutMerge S inside outside x.1 = inside x := by
-- proof
  apply StatMech.FrontierA.finiteCutMerge_inside G S inside outside x

/--
[finiteCutMerge_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutMerge_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool)
  (x : {v : V // v ∉ S}) :
-- imply
  finiteCutMerge S inside outside x.1 = outside x := by
-- proof
  apply StatMech.FrontierA.finiteCutMerge_outside G S inside outside x

/--
[spin_finiteCutMerge_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma spin_finiteCutMerge_inside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool)
  (x : {v : V // v ∈ S}) :
-- imply
  spin (finiteCutMerge S inside outside) x.1 = spin inside x := by
-- proof
  apply StatMech.FrontierA.spin_finiteCutMerge_inside G S inside outside x

/--
[spin_finiteCutMerge_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma spin_finiteCutMerge_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool)
  (x : {v : V // v ∉ S}) :
-- imply
  spin (finiteCutMerge S inside outside) x.1 = spin outside x := by
-- proof
  apply StatMech.FrontierA.spin_finiteCutMerge_outside G S inside outside x

/--
[mk_mem_finiteCutInternalEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma mk_mem_finiteCutInternalEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {x y : V} :
-- imply
  s(x, y) ∈ finiteCutInternalEdges G S ↔ G.Adj x y ∧ x ∈ S ∧ y ∈ S := by
-- proof
  apply StatMech.FrontierA.mk_mem_finiteCutInternalEdges_iff G S x y

/--
[mk_mem_finiteCutExteriorEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma mk_mem_finiteCutExteriorEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {x y : V} :
-- imply
  s(x, y) ∈ finiteCutExteriorEdges G S ↔ G.Adj x y ∧ x ∉ S ∧ y ∉ S := by
-- proof
  apply StatMech.FrontierA.mk_mem_finiteCutExteriorEdges_iff G S x y

/--
[mk_mem_finiteCutCrossEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma mk_mem_finiteCutCrossEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {x y : V} :
-- imply
  s(x, y) ∈ finiteCutCrossEdges G S ↔ G.Adj x y ∧ ((x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S)) := by
-- proof
  apply StatMech.FrontierA.mk_mem_finiteCutCrossEdges_iff G S x y

/--
[sum_cross_bond_finiteCutMerge_eq_boundaryField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma sum_cross_bond_finiteCutMerge_eq_boundaryField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  (∑ e ∈ finiteCutCrossEdges G S, bond (finiteCutMerge S inside outside) e) = ∑ x : {v : V // v ∈ S}, finiteCutBoundaryField G S outside x * spin inside x := by
-- proof
  apply StatMech.FrontierA.sum_cross_bond_finiteCutMerge_eq_boundaryField G S inside outside

/--
[sum_internal_bond_finiteCutMerge_eq_cutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma sum_internal_bond_finiteCutMerge_eq_cutGraph_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  (∑ e ∈ finiteCutInternalEdges G S, bond (finiteCutMerge S inside outside) e) = ∑ e ∈ (finiteCutGraph G S).edgeFinset, bond inside e := by
-- proof
  apply StatMech.FrontierA.sum_internal_bond_finiteCutMerge_eq_cutGraph G S inside outside

/--
[finiteCutInternalEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutInternalEdges_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  finiteCutInternalEdges G S ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierA.finiteCutInternalEdges_subset G S

/--
[finiteCutExteriorEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutExteriorEdges_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  finiteCutExteriorEdges G S ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierA.finiteCutExteriorEdges_subset G S

/--
[finiteCutInternalEdges_disjoint_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutInternalEdges_disjoint_exterior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V} :
-- imply
  Disjoint (finiteCutInternalEdges G S) (finiteCutExteriorEdges G S) := by
-- proof
  apply StatMech.FrontierA.finiteCutInternalEdges_disjoint_exterior G S

/--
[sum_bond_eq_internal_add_cross_add_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma sum_bond_eq_internal_add_cross_add_exterior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {sigma : ConfigSpace V} :
-- imply
  (∑ e ∈ G.edgeFinset, bond sigma e) = (∑ e ∈ finiteCutInternalEdges G S, bond sigma e) + (∑ e ∈ finiteCutCrossEdges G S, bond sigma e) + ∑ e ∈ finiteCutExteriorEdges G S, bond sigma e := by
-- proof
  apply StatMech.FrontierA.sum_bond_eq_internal_add_cross_add_exterior G S sigma

/--
[sum_exterior_bond_finiteCutMerge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma sum_exterior_bond_finiteCutMerge_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside inside' : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  (∑ e ∈ finiteCutExteriorEdges G S, bond (finiteCutMerge S inside outside) e) = ∑ e ∈ finiteCutExteriorEdges G S, bond (finiteCutMerge S inside' outside) e := by
-- proof
  apply StatMech.FrontierA.sum_exterior_bond_finiteCutMerge_eq G S inside inside' outside

/--
[sum_bond_finiteCutMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma sum_bond_finiteCutMerge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  (∑ e ∈ G.edgeFinset, bond (finiteCutMerge S inside outside) e) = (∑ e ∈ (finiteCutGraph G S).edgeFinset, bond inside e) + (∑ x : {v : V // v ∈ S}, finiteCutBoundaryField G S outside x * spin inside x) + ∑ e ∈ finiteCutExteriorEdges G S, bond (finiteCutMerge S inside outside) e := by
-- proof
  apply StatMech.FrontierA.sum_bond_finiteCutMerge G S inside outside

/--
[wJ_finiteCutMerge_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma wJ_finiteCutMerge_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  wJ G.edgeFinset (fun _ => beta) (fun _ => 0) (finiteCutMerge S inside outside) = Real.exp (beta * (∑ e ∈ finiteCutExteriorEdges G S, bond (finiteCutMerge S inside outside) e)) * wJ (finiteCutGraph G S).edgeFinset (fun _ => beta) (fun x => beta * finiteCutBoundaryField G S outside x) inside := by
-- proof
  apply StatMech.FrontierA.wJ_finiteCutMerge_factor G beta S inside outside

/--
[finiteCutConditionalTwoPoint_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutConditionalTwoPoint_le_plus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (outside : {v : V // v ∉ S} → Bool)
  (x y : {v : V // v ∈ S}) :
-- imply
  finiteCutConditionalTwoPoint G beta S outside x y ≤ finiteCutPlusTwoPoint G beta S x y := by
-- proof
  apply StatMech.FrontierA.finiteCutConditionalTwoPoint_le_plus G beta hbeta S outside x y

/--
[finiteCutExteriorFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutExteriorFactor_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  0 < finiteCutExteriorFactor G beta S outside := by
-- proof
  apply StatMech.FrontierA.finiteCutExteriorFactor_pos G beta S outside

/--
[wJ_finiteCutMerge_factor_fixedExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma wJ_finiteCutMerge_factor_fixedExterior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (inside : {v : V // v ∈ S} → Bool)
  (outside : {v : V // v ∉ S} → Bool) :
-- imply
  wJ G.edgeFinset (fun _ => beta) (fun _ => 0) (finiteCutMerge S inside outside) = finiteCutExteriorFactor G beta S outside * wJ (finiteCutGraph G S).edgeFinset (fun _ => beta) (fun x => beta * finiteCutBoundaryField G S outside x) inside := by
-- proof
  apply StatMech.FrontierA.wJ_finiteCutMerge_factor_fixedExterior G beta S inside outside

/--
[finiteCutConditionalTwoPoint_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutConditionalTwoPoint_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (outside : {v : V // v ∉ S} → Bool)
  (x y : {v : V // v ∈ S}) :
-- imply
  finiteCutConditionalTwoPoint G beta S outside x y = finiteCutConditionalPairNumerator G beta S outside x y / finiteCutConditionalZ G beta S outside := by
-- proof
  apply StatMech.FrontierA.finiteCutConditionalTwoPoint_eq_div G beta S outside x y

/--
[ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V} :
-- imply
  ZJ G.edgeFinset (fun _ => beta) (fun _ => 0) = ∑ outside : {v : V // v ∉ S} → Bool, finiteCutExteriorFactor G beta S outside * finiteCutConditionalZ G beta S outside := by
-- proof
  apply StatMech.FrontierA.ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ G beta S

/--
[sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (x y : {v : V // v ∈ S}) :
-- imply
  (∑ sigma : ConfigSpace V, (spin sigma x.1 * spin sigma y.1) * wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma) = ∑ outside : {v : V // v ∉ S} → Bool, finiteCutExteriorFactor G beta S outside * finiteCutConditionalPairNumerator G beta S outside x y := by
-- proof
  apply StatMech.FrontierA.sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator G beta S x y

/--
[expJ_pair_le_finiteCutPlusTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma expJ_pair_le_finiteCutPlusTwoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (x y : {v : V // v ∈ S}) :
-- imply
  expJ G.edgeFinset (fun _ => beta) (fun _ => 0) (fun sigma => spin sigma x.1 * spin sigma y.1) ≤ finiteCutPlusTwoPoint G beta S x y := by
-- proof
  apply StatMech.FrontierA.expJ_pair_le_finiteCutPlusTwoPoint G beta hbeta S x y

/--
[isingTorusTwoPoint_le_finiteCutPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma isingTorusTwoPoint_le_finiteCutPlus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d k : Nat}
  {beta : Real}
  {S : Finset (IsingDyadicTorus d k)}
-- given
  (hbeta : 0 ≤ beta)
  (x y : {v // v ∈ S}) :
-- imply
  isingTorusTwoPoint beta x.1 y.1 ≤ finiteCutPlusTwoPoint (isingTorusGraph d k) beta S x y := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_le_finiteCutPlus G beta hbeta S x y

/--
[finiteCutPlusTwoPoint_eq_vertexFieldTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutPlusTwoPoint_eq_vertexFieldTwoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {S : Finset V}
-- given
  (x y : {v // v ∈ S}) :
-- imply
  finiteCutPlusTwoPoint G beta S x y = vertexFieldTwoPoint (finiteCutGraph G S) beta (unitEdgeCoupling (finiteCutGraph G S)) (finiteCutPlusBoundaryField G S) x y := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusTwoPoint_eq_vertexFieldTwoPoint G beta S x y

/--
[expJ_pair_beta_field_eq_vertexFieldTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma expJ_pair_beta_field_eq_vertexFieldTwoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {field : V → Real}
  {x y : V} :
-- imply
  expJ G.edgeFinset (fun _ => beta) (fun z => beta * field z) (fun sigma => spin sigma x * spin sigma y) = vertexFieldTwoPoint G beta (unitEdgeCoupling G) field x y := by
-- proof
  apply StatMech.FrontierA.expJ_pair_beta_field_eq_vertexFieldTwoPoint G beta field x y

/--
[expJ_pair_const_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma expJ_pair_const_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {e : V ≃ W}
  {beta : Real}
  {fieldV : V → Real}
  {fieldW : W → Real}
  {x y : V}
-- given
  (hadj : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
  (hfield : ∀ x, fieldV x = fieldW (e x)) :
-- imply
  expJ G.edgeFinset (fun _ => beta) fieldV (fun sigma => spin sigma x * spin sigma y) = expJ H.edgeFinset (fun _ => beta) fieldW (fun sigma => spin sigma (e x) * spin sigma (e y)) := by
-- proof
  apply StatMech.FrontierA.expJ_pair_const_relabel G H e hadj beta fieldV fieldW hfield x y

/--
[finiteCutPlusTwoPoint_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutPlusTwoPoint_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {S : Finset V}
  {T : Finset W}
  {beta : Real}
-- given
  (e : {v : V // v ∈ S} ≃ {w : W // w ∈ T})
  (hadj : ∀ x y, (finiteCutGraph G S).Adj x y ↔ (finiteCutGraph H T).Adj (e x) (e y))
  (hfield : ∀ x, finiteCutPlusBoundaryField G S x = finiteCutPlusBoundaryField H T (e x))
  (x y : {v : V // v ∈ S}) :
-- imply
  finiteCutPlusTwoPoint G beta S x y = finiteCutPlusTwoPoint H beta T (e x) (e y) := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusTwoPoint_relabel G H S T e hadj hfield beta x y

/--
[finiteCutPlusTwoPoint_torusImage_eq_gvPlus_of_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean)
-/
@[path]
private lemma finiteCutPlusTwoPoint_torusImage_eq_gvPlus_of_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
  (hfield : ∀ x : {x // x ∈ S}, finiteCutPlusBoundaryField (isingTorusGraph d k) (isingTorusImageFinset k S) (isingTorusImageEquiv S hinj x) = plusBoundaryField S x)
  (a b : {x // x ∈ S}) :
-- imply
  finiteCutPlusTwoPoint (isingTorusGraph d k) beta (isingTorusImageFinset k S) (isingTorusImageEquiv S hinj a) (isingTorusImageEquiv S hinj b) = ∫ omega, spin omega a.1 * spin omega b.1 ∂(gvPlusMeasure S beta 0) := by
-- proof
  apply StatMech.FrontierA.finiteCutPlusTwoPoint_torusImage_eq_gvPlus_of_field G S hS hside hinj hfield beta a b


-- created on 2026-10-23
