/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLexDisagreementComponentMask_seed
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    (sixVertexLexDisagreementComponentMask T omega eta h).vertical
      (sixVertexLexPositiveSeamSeed T omega eta h,
        svFinLast T.height_pos) = true := by
  classical
  simp [sixVertexLexDisagreementComponentMask,
    sixVertexLexPositiveSeamEdge]


theorem sixVertexLocalDisagreementCount_eq_two_or_four
    (p q : SixVertexLocalIncomingPattern)
    (hp : p.Ice) (hq : q.Ice) (hne : p ≠ q) :
    (∑ d, if p d ≠ q d then 1 else 0) = 2 \/
      (∑ d, if p d ≠ q d then 1 else 0) = 4 := by
  decide +revert


end
end StatMech.FrontierD
