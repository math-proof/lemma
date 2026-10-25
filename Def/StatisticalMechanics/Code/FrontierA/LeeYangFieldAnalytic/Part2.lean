/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leeYangComplexFieldLogDerivative
    (beta : ℝ) (h : ℂ) : ℂ :=
  leeYangComplexFieldMagnetizationNumerator G beta h /
    leeYangComplexFieldPartition G beta h

end StatMech.FrontierA
