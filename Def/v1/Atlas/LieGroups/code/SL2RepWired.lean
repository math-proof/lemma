module
public import Theorem.v1.Atlas.LieGroups.code.SL2Classification
public import Theorem.Complex.Nonempty_Realization
public import Inductive.v1.Atlas.LieGroups.code.SL2RepWired


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RepWired.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

noncomputable def ktypeBoundedness (M : SL2GKModule 𝔤 K 𝔨 Ad V) : KTypeBoundedness' :=
  open Classical in
  if BddAbove M.ktypeSet then
    if BddBelow M.ktypeSet then
      KTypeBoundedness'.boundedBoth
    else
      KTypeBoundedness'.boundedAbove
  else
    if BddBelow M.ktypeSet then
      KTypeBoundedness'.boundedBelow
    else
      KTypeBoundedness'.unboundedBoth

end SL2GKModule
