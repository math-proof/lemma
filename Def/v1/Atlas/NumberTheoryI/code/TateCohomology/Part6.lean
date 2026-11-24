module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Def.v1.Atlas.NumberTheoryI.code.Cor2328
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328
public import Theorem.v1.Atlas.NumberTheoryI.code.TateCohomology.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

def invEquivTrivFinFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants ≃ₗ[ℤ] (Fin n → ℤ) :=
  (LinearEquiv.ofEq _ _ (by ext x; simp [Representation.mem_invariants])).trans
    Submodule.topEquiv

end TateCohomology
end
