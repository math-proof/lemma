/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

instance cubicalDualEquivPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

end
end StatMech.FrontierA
