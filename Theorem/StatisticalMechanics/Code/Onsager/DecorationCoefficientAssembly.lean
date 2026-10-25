/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


theorem ons_decCycle_remainder_originalHomology_isotropic
    (L : ℕ) [Fact (2 < L)]
    {d : ons_Dart L} (q : (ons_decGraph L).Walk d d)
    (hq : q.IsCycle) (R : ons_DecoratedEvenSubgraph L)
    (hzero : ∀ v ∈ q.support, incCount R.1 v = 0) :
    ons_homologyIntersection
        (ons_evenHomology L (ons_walkOriginalEdges q))
        (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) = 0 := by
  classical
  obtain ⟨ι, hiFintype, hiDecidable, base, p, hpcycle,
      hcover, hedgeDisj, hvertDisj⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L R
  letI : Fintype ι := hiFintype
  letI : DecidableEq ι := hiDecidable
  have hhomology :
      ons_evenHomology L (ons_originalEdgesOfDecorated L R) =
        ∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i)) := by
    simpa only [ons_walkOriginalEdges, ons_walkExternalEdges] using
      ons_originalHomology_biUnion R
        (fun i ↦ (p i).edges.toFinset) hcover hedgeDisj
  rw [hhomology]
  rw [show (∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i))) =
      ∑ i ∈ Finset.univ,
        ons_evenHomology L (ons_walkOriginalEdges (p i)) by simp]
  rw [ons_homologyIntersection_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  have hpR : (p i).edges.toFinset ⊆ R.1 := by
    intro edge hedge
    rw [hcover, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hedge⟩
  have hverts : Disjoint q.toSubgraph.verts (p i).toSubgraph.verts :=
    ons_cycle_vertices_disjoint_of_incCount_zero
      (ons_decGraph L) q (p i) (hpcycle i) R.1 hzero hpR
  exact ons_decCycles_originalHomology_isotropic
    L q (p i) hq (hpcycle i) hverts


theorem ons_decoratedWeightedSpinWeight_split_eq_neg_cycleWeight
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) (d : ons_Dart L)
    (hd : s(d, ons_dartRev L d) ∈ D.1)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ∃ (q : (ons_decGraph L).Walk d d)
      (R : ons_DecoratedEvenSubgraph L),
      q.IsCycle ∧ q.snd = ons_dartRev L d ∧
      D.1 = q.edges.toFinset ∪ R.1 ∧
      Disjoint q.edges.toFinset R.1 ∧
      (∀ v ∈ q.support, incCount R.1 v = 0) ∧
      incCount R.1 d = 0 ∧
      incCount R.1 (ons_dartRev L d) = 0 ∧
      ons_decoratedWeightedSpinWeight L weight a b D =
        -ons_edgeWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            (ons_decCycleFirstReturn q) *
          ons_decoratedWeightedSpinWeight L weight a b R := by
  obtain ⟨q, R, hq, hsnd, hsplit, hdisj, hzero, hzeroD, hzeroRev⟩ :=
    ons_decorated_split_cycle_at_external L D d hd
  have hisotropic :=
    ons_decCycle_remainder_originalHomology_isotropic L q hq R hzero
  have hfactor := ons_decoratedWeightedSpinWeight_split_of_isotropic
    L D R q hsplit hdisj weight a b hisotropic
  have hcycle := ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    q hq hsnd weight a b
  refine ⟨q, R, hq, hsnd, hsplit, hdisj, hzero, hzeroD, hzeroRev, ?_⟩
  rw [hfactor, hcycle]
  ring


end StatMech.Onsager
