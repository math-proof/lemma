/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Def.StatisticalMechanics.Code.Walls.bc39spanning
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc39_connected_removeSites_of_walk_avoids (S : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d} (p : (openSubgraph d ω).Walk a b)
    (hp : ∀ v ∈ p.support, v ∉ S) : Connected d (removeSites S ω) a b :=
  ⟨bc39_transferWalk S ω p hp⟩


theorem bc39_armAdj_edge_of_walk_avoids (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {a b : Site d}
    (hab : a ≠ b) (p : (openSubgraph d ω).Walk a b)
    (hint : ∀ v ∈ p.support, v ∈ tfc_trifFinset ω n → v = a ∨ v = b) :
    bc37_ArmAdjacent ω n a b := by
  refine ⟨hab, ⟨p⟩, ?_⟩
  unfold bc37_cutExcept
  apply bc39_connected_removeSites_of_walk_avoids _ ω p
  intro v hv hmem
  rw [Finset.mem_erase, Finset.mem_erase] at hmem
  obtain ⟨hvb, hva, hvT⟩ := hmem
  rcases hint v hv hvT with rfl | rfl
  · exact hva rfl
  · exact hvb rfl


theorem bc39_reach_of_walk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ (k : ℕ) {a b : Site d} (haT : a ∈ tfc_trifFinset ω n) (hbT : b ∈ tfc_trifFinset ω n)
      (p : (openSubgraph d ω).Walk a b), p.length ≤ k →
      (bc37_armAdjGraph ω n).Reachable ⟨a, haT⟩ ⟨b, hbT⟩ := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro a b haT hbT p hlen
    by_cases hab : a = b
    · subst hab
      exact SimpleGraph.Reachable.refl _
    · by_cases hint : ∀ v ∈ p.support, v ∈ tfc_trifFinset ω n → v = a ∨ v = b
      · 
        have hadj : (bc37_armAdjGraph ω n).Adj ⟨a, haT⟩ ⟨b, hbT⟩ :=
          bc39_armAdj_edge_of_walk_avoids ω n hab p hint
        exact hadj.reachable
      · 
        push Not at hint
        obtain ⟨c, hcsupp, hcT, hca, hcb⟩ := hint
        have hsum : (p.takeUntil c hcsupp).length + (p.dropUntil c hcsupp).length = p.length := by
          rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec]
        have htake_len : (p.takeUntil c hcsupp).length < k := by
          have hdrop_pos : 0 < (p.dropUntil c hcsupp).length := by
            rcases Nat.eq_zero_or_pos (p.dropUntil c hcsupp).length with h0 | hpos
            · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hcb
            · exact hpos
          omega
        have hdrop_len : (p.dropUntil c hcsupp).length < k := by
          have htake_pos : 0 < (p.takeUntil c hcsupp).length := by
            rcases Nat.eq_zero_or_pos (p.takeUntil c hcsupp).length with h0 | hpos
            · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h0) hca.symm
            · exact hpos
          omega
        have r1 := IH _ htake_len haT hcT (p.takeUntil c hcsupp) (le_refl _)
        have r2 := IH _ hdrop_len hcT hbT (p.dropUntil c hcsupp) (le_refl _)
        exact r1.trans r2


theorem bc39_armAdjSpanning (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc38_ArmAdjSpanning ω n := by
  classical
  intro a b hconn
  obtain ⟨p⟩ := hconn
  exact bc39_reach_of_walk ω n p.length a.2 b.2 p (le_refl _)


theorem bc39_armCutGeometry_false_of_armAdjacent (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {t s : Site d} (htbox : t ∈ box d n) (htri : IsTrifurcation d ω t)
    (hadj : bc37_ArmAdjacent ω n t s) : ¬ bc38_ArmCutGeometry ω n := by
  rintro ⟨b, _hdata, hclauses⟩
  obtain ⟨_hloc, hself, hfun⟩ := hclauses t s htbox htri hadj
  exact hself (hfun t hadj.1)


end StatMech.Walls
