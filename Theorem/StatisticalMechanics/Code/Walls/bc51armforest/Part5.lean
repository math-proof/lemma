/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection.Part2
import Instance.StatisticalMechanics.Code.Walls.bc51armforest.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


namespace Bc51Witness

theorem cycleG_not_acyclic : ¬ cycleG.IsAcyclic := by
  
  intro hac
  have h02 : cycleG.Adj 0 2 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE catE; decide
  have h24 : cycleG.Adj 2 4 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE; decide
  have h41 : cycleG.Adj 4 1 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE catE; decide
  have h10 : cycleG.Adj 1 0 := by
    rw [cycleG, fromRel_adj]; refine ⟨by decide, ?_⟩; left; unfold cycleE catE; decide
  
  refine hac (Walk.cons h02 (Walk.cons h24 (Walk.cons h41 (Walk.cons h10 Walk.nil)))) ?_
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil]
    decide
  · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
    decide


theorem catG_subgraph_acyclic {H : SimpleGraph (Fin 6)} (hsub : H ≤ catG) : H.IsAcyclic :=
  bc51_subgraph_isAcyclic hsub catG_isTree.isAcyclic

end Bc51Witness


theorem bc51_forestCover_nonvacuous_nilWalk {x a : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} (T : SimpleGraph (Site d))
    (hax : a ≠ x) :
    let w : (openSubgraph d (removeSite x ω)).Walk a a := Walk.nil
    x ∉ w.support ∧
      (∀ e, e ∈ (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges → e ∈ T.edgeSet) := by
  refine ⟨?_, ?_⟩
  · simpa using (Ne.symm hax)
  · intro e he
    simp only [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.map_nil] at he
    exact absurd he (List.not_mem_nil)


theorem bc51_globalArmForest_nonvacuous_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    bc51_GlobalArmForest ω n :=
  bc51_globalArmForest_star ω n a hsingle hxbox htri hadj habdry hxne hainj hsep


theorem bc51_burton_keane_bernoulli_of_globalArmForest (hd : 1 ≤ d) (p : NNReal) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc51_GlobalArmForest ω n)
    (hroute : ∀ n : ℕ,
      0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) →
        ∃ a₁ a₂ a₃ : Site d,
          0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
            (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc50_burton_keane_bernoulli_of_armForest hd p hp1 hp0
    (fun ω n => bc51_armForestReaching_of_globalArmForest ω n (harm ω n)) hroute

end StatMech.Walls
