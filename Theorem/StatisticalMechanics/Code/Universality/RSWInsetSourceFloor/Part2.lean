/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part2
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_affineFlipYEdge_symm_apply (k : Int) (e : Sym2 (Site 2)) :
    (rlc_affineFlipYEdge k).symm e = e.map (rlc_affineFlipY k) := by
  simp [rlc_affineFlipYEdge, sym2Congr, rlc_affineFlipY]

end
end StatMech.Universality
