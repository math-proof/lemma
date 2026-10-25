/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexFulmekPerronBound (n r : Nat) : Real :=
  2 ^ r * ∏ j : Fin r,
    (1 + Real.cos (Real.pi * (2 * (j : Real) + 1) / (n + 2 * r)))

end
end StatMech.FrontierD
