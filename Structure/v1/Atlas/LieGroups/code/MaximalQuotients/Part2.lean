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
import Def.v1.Atlas.LieGroups.code.MaximalQuotients


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

structure IsHarishChandraBimodule (M : LieBimodule R 𝔤) : Prop where
  locally_finite : ∀ (m : M.carrier), ∃ (S : Submodule R M.carrier),
    Module.Finite R S ∧ m ∈ S ∧
    ∀ (x : 𝔤), ∀ (s : M.carrier), s ∈ S → M.adjointAction x s ∈ S

structure LieBimodule.HasInfinitesimalCharacterPair (M : LieBimodule R 𝔤)
    (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) : Prop where
  left_char : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.leftAction (z : UniversalEnvelopingAlgebra R 𝔤) m = θ z • m
  right_char : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) m = χ z • m

end
