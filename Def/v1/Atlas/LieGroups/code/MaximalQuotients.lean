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
import Structure.v1.Atlas.LieGroups.code.MaximalQuotients


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] LieBimodule.instAddCommGroup LieBimodule.instModule

def LieBimodule.adjointAction (M : LieBimodule R 𝔤) (x : 𝔤) :
    Module.End R M.carrier :=
  M.leftAction (UniversalEnvelopingAlgebra.ι R x) -
  M.rightAction (MulOpposite.op (UniversalEnvelopingAlgebra.ι R x))

def LieBimodule.IsSubBimodule (M : LieBimodule R 𝔤) (S : Submodule R M.carrier) : Prop :=
  (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (s : M.carrier), s ∈ S → M.leftAction u s ∈ S) ∧
  (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (s : M.carrier), s ∈ S → M.rightAction u s ∈ S)

def LieBimodule.IsIrreducible (M : LieBimodule R 𝔤) : Prop :=
  (∃ m : M.carrier, m ≠ 0) ∧
  ∀ (S : Submodule R M.carrier), M.IsSubBimodule S → S = ⊥ ∨ S = ⊤

end
