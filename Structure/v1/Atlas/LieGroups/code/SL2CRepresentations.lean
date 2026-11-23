/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2CRepresentations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
public import Theorem.Nat.basisHC.eq.SMul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Abbrev.v1.Atlas.LieGroups.code.SL2CRepresentations


public noncomputable section

open Complex

open scoped Classical

structure SL2C_UnitaryRep where
  V : Type*
  [instNACG : NormedAddCommGroup V]
  [instIPS : InnerProductSpace ℂ V]
  [instCS : CompleteSpace V]
  action : SL2C →* V ≃ₗᵢ[ℂ] V

end
