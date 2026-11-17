/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_runframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc_toprowrun.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc_runnoup
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe
public section

open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


structure jc2_RunFrame (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  
  isRun : jc_IsTopRowRun K c len
  
  no_up : ∀ j : ℤ, (c + ![j, 1]) ∉ K
  
  left_out : (c + ![(-1 : ℤ), 0]) ∉ K
  
  right_out : (c + ![len + 1, 0]) ∉ K


end Walls
end StatMech
