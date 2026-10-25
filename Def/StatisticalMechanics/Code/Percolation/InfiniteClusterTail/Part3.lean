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
import Structure.StatisticalMechanics.Code.Percolation.InfiniteClusterTail
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}

noncomputable def infiniteClusterTailData
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d))
    (hxK : x ∈ K) : InfiniteClusterTailData omega K x := by
  classical
  exact Classical.choice (by
    obtain ⟨u, v, T, hu, hv, huv, hvT, hTinf, hTsub, hTconn⟩ :=
      infiniteCluster_has_open_exit_to_infinite_tail omega x hinf K hxK
    exact ⟨⟨u, v, T, hu, hv, huv, hvT, hTinf, hTsub, hTconn⟩⟩)


end StatMech.Percolation
