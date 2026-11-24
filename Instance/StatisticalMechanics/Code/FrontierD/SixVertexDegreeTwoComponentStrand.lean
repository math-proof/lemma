module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
public import Mathlib.Data.Finset.SymmDiff
open Finset SimpleGraph
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

instance degreeTwoComponentStrandDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p


end
end StatMech.FrontierD
