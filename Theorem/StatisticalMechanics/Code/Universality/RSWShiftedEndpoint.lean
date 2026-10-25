/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
import Abbrev.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


@[simp] theorem rlc_shiftedEndpointPreimage_zero (x : Site 2) :
    rlc_shiftedEndpointPreimage x 0 = -x 0 := rfl

@[simp] theorem rlc_shiftedEndpointPreimage_one (x : Site 2) :
    rlc_shiftedEndpointPreimage x 1 = x 1 - 1 := rfl


end Universality
end StatMech
