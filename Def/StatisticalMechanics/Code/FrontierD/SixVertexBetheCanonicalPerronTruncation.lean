/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogNumerator (c x : Real) : Real :=
  (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x

def sixVertexBetheLogDenominator (x : Real) : Real :=
  2 - 2 * Real.cos x


def sixVertexRegularizedBetheLogKernel
    (c epsilon x : Real) : Real :=
  (1 / 2 : Real) *
    (Real.log (sixVertexBetheLogNumerator c x) -
      Real.log (sixVertexBetheLogDenominator x + epsilon))

end
end StatMech.FrontierD
