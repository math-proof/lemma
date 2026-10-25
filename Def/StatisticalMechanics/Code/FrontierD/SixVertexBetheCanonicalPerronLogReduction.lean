/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLogReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogObservable (c p : Real) : Real :=
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖

end
end StatMech.FrontierD
