/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part3
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


theorem sctBoxInclusionEquiv_adj (d : ℕ) {n m : ℕ} (hnm : n ≤ m)
    (a b : sctBox d n) :
    (sctBoxGraph d n).Adj a b ↔
      ((sctBoxGraph d m).comap
        (Subtype.val : {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)).Adj
        (sctBoxInclusionEquiv d hnm a) (sctBoxInclusionEquiv d hnm b) := by
  simp [sctBoxGraph, sctBoxInclusionEquiv, SimpleGraph.comap_adj]


end Sharpness
end StatMech
