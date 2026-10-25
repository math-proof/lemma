/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Percolation.InfiniteClusterTail
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}

noncomputable instance tailClusterGraphLocallyFinite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    SimpleGraph.LocallyFinite (tailClusterGraph omega x) := by
  intro v
  let f : (tailClusterGraph omega x).neighborSet v ->
      (hypercubicLattice d).neighborSet v.1 := fun w =>
    ⟨w.1.1, (openSubgraph_le omega) w.2⟩
  exact Fintype.ofInjective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (hypercubicLattice d).neighborSet v.1 => (z : Site d)) h)


instance tailClusterGraphPreconnected
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    Fact (tailClusterGraph omega x).Preconnected := ⟨by
  intro u v
  have huv : Connected d omega u.1 v.1 := (Connected.symm u.2).trans v.2
  obtain ⟨w⟩ := huv
  exact StatMech.Lattice.walk_induce_reachable (openSubgraph d omega)
    (cluster d omega x) w (fun z hz => by
      have hzx : z ∈ cluster d omega v.1 := ava_support_mem_cluster omega w hz
      rwa [← cluster_eq_of_connected v.2] at hzx) u.2 v.2⟩


end StatMech.Percolation
