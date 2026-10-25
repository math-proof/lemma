/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Def.StatisticalMechanics.Code.Walls.bc38acyclic.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc38_armAdjAcyclic_iff_path_unique (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc38_ArmAdjAcyclic ω n ↔
      ∀ ⦃a b⦄ (p q : (bc37_armAdjGraph ω n).Path a b), p = q :=
  SimpleGraph.isAcyclic_iff_path_unique


set_option linter.unusedDecidableInType false in


theorem bc38_unique_closer_neighbour_of_acyclic {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hac : G.IsAcyclic) {root v u₁ u₂ : V} (h1 : G.Adj v u₁) (h2 : G.Adj v u₂)
    (hd1 : G.dist root u₁ < G.dist root v) (hd2 : G.dist root u₂ < G.dist root v) :
    u₁ = u₂ := by
  have hvr : G.Reachable root v := SimpleGraph.Reachable.of_dist_ne_zero (by omega)
  obtain ⟨p1, hpp1, hlp1⟩ := (hvr.trans h1.reachable).exists_path_of_dist
  obtain ⟨p2, hpp2, hlp2⟩ := (hvr.trans h2.reachable).exists_path_of_dist
  have hv1 : v ∉ p1.support := fun hv => by
    have hle : G.dist root v ≤ (p1.takeUntil v hv).length := SimpleGraph.dist_le _
    have := p1.length_takeUntil_le hv; omega
  have hv2 : v ∉ p2.support := fun hv => by
    have hle : G.dist root v ≤ (p2.takeUntil v hv).length := SimpleGraph.dist_le _
    have := p2.length_takeUntil_le hv; omega
  have heq : (⟨p1.concat h1.symm, hpp1.concat hv1 h1.symm⟩ : G.Path root v)
      = ⟨p2.concat h2.symm, hpp2.concat hv2 h2.symm⟩ :=
    SimpleGraph.isAcyclic_iff_path_unique.mp hac _ _
  have heqw : p1.concat h1.symm = p2.concat h2.symm := Subtype.mk.inj heq
  calc u₁ = (p1.concat h1.symm).penultimate := by simp [SimpleGraph.Walk.penultimate_concat]
    _ = (p2.concat h2.symm).penultimate := by rw [heqw]
    _ = u₂ := by simp [SimpleGraph.Walk.penultimate_concat]


theorem bc38_unique_armParent (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hac : bc38_ArmAdjAcyclic ω n)
    {root v u₁ u₂ : {x : Site d // x ∈ tfc_trifFinset ω n}}
    (h1 : (bc37_armAdjGraph ω n).Adj v u₁) (h2 : (bc37_armAdjGraph ω n).Adj v u₂)
    (hd1 : (bc37_armAdjGraph ω n).dist root u₁ < (bc37_armAdjGraph ω n).dist root v)
    (hd2 : (bc37_armAdjGraph ω n).dist root u₂ < (bc37_armAdjGraph ω n).dist root v) :
    u₁ = u₂ :=
  bc38_unique_closer_neighbour_of_acyclic (bc37_armAdjGraph ω n) hac h1 h2 hd1 hd2


end StatMech.Walls
