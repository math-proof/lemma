/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Lie.OfAssociative


noncomputable section

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
