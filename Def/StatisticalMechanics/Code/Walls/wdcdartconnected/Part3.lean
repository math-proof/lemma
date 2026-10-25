/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Theorem.StatisticalMechanics.Code.Walls.wdcdartconnected.Part2
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


noncomputable def wdc_pick (K : Set (Site 2)) (v : {x : Site 2 // x ∈ wdc_boundaryLayer K}) :
    {e : Dart // IsBoundaryDart K e} :=
  (wdc_layer_isHead K v.2).choose

end Wots
end StatMech
