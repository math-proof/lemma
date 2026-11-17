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
public import Def.v1.Atlas.LieGroups.code.MaximalQuotients


public noncomputable section

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
