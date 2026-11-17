/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Structure.v1.Atlas.LieGroups.code.BeilinsonBernstein

@[expose] public section

open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

universe u

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

attribute [instance] AbCat.instCat

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

def filtPred {α : Type*} [AddCommMonoid α] [Module ℂ α]
    (F : ℕ → Submodule ℂ α) : ℕ → Submodule ℂ α
  | 0 => ⊥
  | n + 1 => F n

end
end BeilinsonBernstein
