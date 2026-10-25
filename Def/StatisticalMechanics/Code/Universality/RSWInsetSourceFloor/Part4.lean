/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part3
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_affineFlipYInducedHom (a b c d k : Int)
    (hcd : c + d = k) (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraphInduce 2 omega (rect a b c d) →g
      openSubgraphInduce 2 (rlc_affineFlipYConfig k omega) (rect a b c d) where
  toFun := fun x =>
    ⟨rlc_affineFlipY k (x : Site 2),
      (rlc_mem_rect_affineFlipY a b c d k hcd x).mp x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    change IsOpenEdge 2 (rlc_affineFlipYConfig k omega)
      (rlc_affineFlipY k (x : Site 2)) (rlc_affineFlipY k (y : Site 2))
    rw [rlc_isOpenEdge_affineFlipY]
    simpa using hxy

end
end StatMech.Universality
