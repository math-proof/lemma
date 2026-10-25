/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part2
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


theorem source_injective
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    Function.Injective (fun positive =>
      base.source positive hmiddle_pos hmiddle_lt) := by
  intro first second heq
  apply base.mask_injective
  apply sixVertexTorusSwitchFirst_injective_on_fullMasks
    (base.mask_full first) (base.mask_full second)
  have harrows := congrArg (fun source => source.1.1) heq
  change sixVertexTorusSwitchFirst (base.mask first) base.first base.second =
    sixVertexTorusSwitchFirst (base.mask second) base.first base.second at harrows
  exact harrows

theorem target_injective
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k) :
    Function.Injective base.target := by
  intro first second heq
  apply base.mask_injective
  apply sixVertexTorusSwitchFirst_injective_on_fullMasks
    (base.mask_full first) (base.mask_full second)
  have harrows := congrArg (fun target => target.1.1) heq
  change sixVertexTorusSwitchFirst (base.mask first) base.first base.second =
    sixVertexTorusSwitchFirst (base.mask second) base.first base.second at harrows
  exact harrows


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
