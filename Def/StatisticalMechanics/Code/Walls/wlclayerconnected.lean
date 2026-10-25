/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wdcdartconnected.Part4
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


def wlc_layerCell (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    {v : Site 2 // v ∈ wdc_boundaryLayer K} :=
  ⟨d.1.head, wdc_head_mem_layer K d⟩

end Wots
end StatMech
