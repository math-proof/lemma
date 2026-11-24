module
public import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
public import Theorem.Int.Any_EqUeaAction
public import Theorem.Fin.Any_Eq.of.Ne_0
public import Theorem.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
public import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
public import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
public import Abbrev.v1.Atlas.LieGroups.code.DufloJoseph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def DominantWeights (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ) (chev : ChevalleyData Δ) : Set (Δ.𝔥 →ₗ[R] R) :=
  { γ | IsDominantIntegralWeight Δ rd chev γ }

end
