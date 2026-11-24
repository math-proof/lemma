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
public import Theorem.v1.Atlas.NumberTheoryI.code.TateCohomology


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

def tateH0_equiv_zmod {G₀ : Type} [Group G₀] [Fintype G₀] :
    tateH0 (Rep.trivial ℤ G₀ ℤ) ≃ ZMod (Fintype.card G₀) :=
  (Submodule.Quotient.equiv _ _ invEquivTrivInt map_normImage_trivInt).toEquiv.trans
    ((Int.quotientSpanEquivZMod (Fintype.card G₀ : ℤ)).toEquiv.trans
      (Equiv.cast (by simp [Int.natAbs_natCast])))

def Rep.trivialHom {G₀ : Type*} [Monoid G₀]
    {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (f : M →ₗ[ℤ] N) :
    Rep.trivial ℤ G₀ M ⟶ Rep.trivial ℤ G₀ N :=
  Rep.ofHom ⟨f, fun g => by ext x; simp [Representation.trivial]⟩

end TateCohomology
end
