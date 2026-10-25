/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredVertexCrossFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentFineRowProfile
open Finset


namespace StatMech.FrontierD

noncomputable section

instance sixVertexColoredVertexCrossFineRowProfilePropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p


end
end StatMech.FrontierD
