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
import Structure.v1.Atlas.LieGroups.code.MaximalQuotients.Part3


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

def maximalQuotientIdeal
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    TwoSidedIdeal (UniversalEnvelopingAlgebra R 𝔤) :=
  TwoSidedIdeal.span
    { x | ∃ (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      x = (z : UniversalEnvelopingAlgebra R 𝔤) - algebraMap R _ (χ z) }

end
