/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Def.StatisticalMechanics.Code.Universality.RSWRayTransport
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


@[simp] theorem rlc_primalDualReflect_zero (x : Site 2) :
    rlc_primalDualReflect x 0 = -x 0 := by
  rfl

@[simp] theorem rlc_primalDualReflect_one (x : Site 2) :
    rlc_primalDualReflect x 1 = x 1 + 1 := by
  rfl

@[simp] theorem rlc_primalDualReflect_symm_zero (x : Site 2) :
    rlc_primalDualReflect.symm x 0 = -x 0 := by
  rfl

@[simp] theorem rlc_primalDualReflect_symm_one (x : Site 2) :
    rlc_primalDualReflect.symm x 1 = x 1 - 1 := by
  rfl


end Universality
end StatMech
