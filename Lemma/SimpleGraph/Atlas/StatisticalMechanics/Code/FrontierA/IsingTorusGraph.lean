import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
open Finset StatMech StatMech.FrontierA


/--
[isingTorusStep_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusStep_ne_zero_eq
  {d k : Nat}
  {i : Fin d} :
-- imply
  (isingTorusStep i : IsingDyadicTorus d k) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusStep_ne_zero i

/--
[isingTorusGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusGraph_adj_iff_eq
  {d k : Nat}
  {x y : IsingDyadicTorus d k} :
-- imply
  (isingTorusGraph d k).Adj x y ↔ ∃ i : Fin d, y = x + isingTorusStep i ∨ x = y + isingTorusStep i := by
-- proof
  apply StatMech.FrontierA.isingTorusGraph_adj_iff x y

/--
[isingTorusIndexedEdge_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusIndexedEdge_mem_edgeFinset_eq
  {d k : Nat}
  {p : IsingDyadicTorus d k × Fin d} :
-- imply
  isingTorusIndexedEdge p ∈ (isingTorusGraph d k).edgeFinset := by
-- proof
  apply StatMech.FrontierA.isingTorusIndexedEdge_mem_edgeFinset p

/--
[isingTorusIndexedEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusIndexedEdge_injective_eq
  {d k : Nat} :
-- imply
  Function.Injective (isingTorusIndexedEdge : IsingDyadicTorus d k × Fin d → Sym2 (IsingDyadicTorus d k)) := by
-- proof
  apply StatMech.FrontierA.isingTorusIndexedEdge_injective

/--
[isingTorusIndexedEdge_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusIndexedEdge_surjective_eq
  {d k : Nat} :
-- imply
  Function.Surjective (fun p : IsingDyadicTorus d k × Fin d => (⟨isingTorusIndexedEdge p, isingTorusIndexedEdge_mem_edgeFinset p⟩ : (isingTorusGraph d k).edgeFinset)) := by
-- proof
  apply StatMech.FrontierA.isingTorusIndexedEdge_surjective

/--
[isingTorus_bond_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorus_bond_sum_eq_eq
  {d k : Nat}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  (∑ e ∈ (isingTorusGraph d k).edgeFinset, bond sigma e) = ∑ x : IsingDyadicTorus d k, ∑ i : Fin d, spin sigma x * spin sigma (x + isingTorusStep i) := by
-- proof
  apply StatMech.FrontierA.isingTorus_bond_sum_eq sigma

/--
[isingTorusDirichlet_spin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusDirichlet_spin_eq_eq
  {d k : Nat}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  isingTorusDirichlet (isingTorusSpinField sigma) = 2 * Fintype.card (IsingDyadicTorus d k) * d - 2 * ∑ e ∈ (isingTorusGraph d k).edgeFinset, bond sigma e := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_spin_eq sigma

/--
[isingTorus_zero_weight_eq_graph_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorus_zero_weight_eq_graph_weight_eq
  {d k : Nat}
  {beta : Real}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) = Real.exp (-beta * (Fintype.card (IsingDyadicTorus d k) : Real) * d) * isingWeight (isingTorusGraph d k) beta 0 sigma := by
-- proof
  apply StatMech.FrontierA.isingTorus_zero_weight_eq_graph_weight beta sigma

/--
[isingTorusShiftedPartition_zero_eq_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_zero_eq_graph_eq
  {d k : Nat}
  {beta : Real} :
-- imply
  isingTorusShiftedPartition (d := d) (k := k) beta 0 = Real.exp (-beta * (Fintype.card (IsingDyadicTorus d k) : Real) * d) * isingZ (isingTorusGraph d k) beta 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_zero_eq_graph beta

/--
[isingTorusTwoPoint_eq_twoPointJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusTwoPoint_eq_twoPointJ_eq
  {d k : Nat}
  {beta : Real}
  {x y : IsingDyadicTorus d k} :
-- imply
  isingTorusTwoPoint beta x y = twoPointJ (isingTorusGraph d k) beta (fun _ => 1) x y := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_eq_twoPointJ beta x y

/--
[isingTorusTwoPoint_eq_twoPointJ_unitEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusTwoPoint_eq_twoPointJ_unitEdge_eq
  {d k : Nat}
  {beta : Real}
  {x y : IsingDyadicTorus d k} :
-- imply
  isingTorusTwoPoint beta x y = twoPointJ (isingTorusGraph d k) beta (unitEdgeCoupling (isingTorusGraph d k)) x y := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_eq_twoPointJ_unitEdge beta x y

/--
[isingTorusTwoPoint_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusTwoPoint_le_one_eq
  {d k : Nat}
  {beta : Real}
  {x y : IsingDyadicTorus d k} :
-- imply
  isingTorusTwoPoint beta x y ≤ 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_le_one beta x y

/--
[isingTorusTwoPoint_sum_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorusTwoPoint_sum_translate_eq
  {d k : Nat}
  {beta : Real}
  {y : IsingDyadicTorus d k} :
-- imply
  (∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta y z) = ∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_sum_translate beta y

/--
[isingTorus_susceptibility_le_of_simon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGraph.lean)
-/
@[path]
private lemma isingTorus_susceptibility_le_of_simon_eq
  {d k : Nat}
  {beta : Real}
  {S : Finset (IsingDyadicTorus d k)}
-- given
  (hbeta : 0 ≤ beta)
  (hzero : 0 ∈ S)
  (hphi : simonConst S (simonWeightPair (isingTorusGraph d k) beta (unitEdgeCoupling (isingTorusGraph d k)) S 0) (Finset.univ \ S) < 1) :
-- imply
  (∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z) ≤ (S.card : Real) / (1 - simonConst S (simonWeightPair (isingTorusGraph d k) beta (unitEdgeCoupling (isingTorusGraph d k)) S 0) (Finset.univ \ S)) := by
-- proof
  apply StatMech.FrontierA.isingTorus_susceptibility_le_of_simon beta hbeta S hzero hphi


-- created on 2026-10-23
