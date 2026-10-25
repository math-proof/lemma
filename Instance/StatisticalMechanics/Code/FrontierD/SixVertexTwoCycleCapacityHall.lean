/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

instance twoCycleCapacityHallDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p


end
end StatMech.FrontierD
