/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Lie.OfAssociative


public noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

structure LieBimodule (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] where
  carrier : Type*
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  leftAction : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R carrier
  rightAction : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ →ₐ[R] Module.End R carrier
  actions_commute : ∀ (u : UniversalEnvelopingAlgebra R 𝔤)
    (v : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : carrier),
    leftAction u (rightAction v m) = rightAction v (leftAction u m)

end
