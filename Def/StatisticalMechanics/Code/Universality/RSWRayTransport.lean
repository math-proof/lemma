/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWRayTransport
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_primalDualReflectFun (x : Site 2) : Site 2 := ![-x 0, x 1 + 1]


def rlc_primalDualReflectInvFun (x : Site 2) : Site 2 := ![-x 0, x 1 - 1]


def rlc_primalDualReflect : Site 2 ≃ Site 2 where
  toFun := rlc_primalDualReflectFun
  invFun := rlc_primalDualReflectInvFun
  left_inv x := by
    ext i
    fin_cases i <;> simp [rlc_primalDualReflectFun,
      rlc_primalDualReflectInvFun]
  right_inv x := by
    ext i
    fin_cases i <;> simp [rlc_primalDualReflectFun,
      rlc_primalDualReflectInvFun]

end Universality
end StatMech
