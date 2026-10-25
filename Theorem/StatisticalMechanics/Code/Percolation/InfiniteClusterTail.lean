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
import Instance.StatisticalMechanics.Code.Percolation.InfiniteClusterTail
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}

theorem infiniteCluster_component_after_finset
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d)) :
    ∃ D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K),
      D.supp.Infinite := by
  letI : Infinite (tailClusterVertex omega x) := hinf.to_subtype
  let e : (tailClusterGraph omega x).end :=
    ⟨(SimpleGraph.nonempty_ends_of_infinite (tailClusterGraph omega x)).choose,
      (SimpleGraph.nonempty_ends_of_infinite (tailClusterGraph omega x)).choose_spec⟩
  let D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K) :=
    (e : (j : (Finset (tailClusterVertex omega x))ᵒᵖ) →
      (tailClusterGraph omega x).componentComplFunctor.obj j)
      (Opposite.op (tailClusterCut omega x K))
  exact ⟨D, SimpleGraph.end_componentCompl_infinite
    (tailClusterGraph omega x) e (Opposite.op (tailClusterCut omega x K))⟩

end StatMech.Percolation
