/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalDensityPerronInitialLogContribution
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (2 * ∑ j : Fin (k + 1) with j.val < J,
      Real.log ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j))‖) /
    (sixVertexFourWidth 0 k : Real)

end
end StatMech.FrontierD
