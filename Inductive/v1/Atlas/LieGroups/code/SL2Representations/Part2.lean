/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
import Lemma.Complex.In_WeightSpace.is.H.eq.SMul
import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.KTypeDecomposition.Part3
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Structure.v1.Atlas.LieGroups.code.SL2Representations
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

open Complex Module

attribute [instance] SL2IrredGKModule.Realization.instAddCommGroup
  SL2IrredGKModule.Realization.instModule
  SL2IrredGKModule.Realization.instLieRingModule
  SL2IrredGKModule.Realization.instLieModule

inductive KTypeBoundedness where
  | boundedBoth
  | unboundedBoth
  | boundedBelow
  | boundedAbove

end
