/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Mathlib.Data.Finset.SymmDiff
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

instance degreeTwoComponentStrandDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p


end
end StatMech.FrontierD
