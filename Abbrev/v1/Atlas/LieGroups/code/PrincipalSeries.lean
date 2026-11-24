module
public import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
public import Theorem.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
public import Theorem.Int.IsInQPlus0
public import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Def.v1.Atlas.LieGroups.code.PrincipalSeries


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

abbrev liftAct (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (x : UniversalEnvelopingAlgebra R 𝔤) (v : V) : V :=
  (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 V)) x v

end
