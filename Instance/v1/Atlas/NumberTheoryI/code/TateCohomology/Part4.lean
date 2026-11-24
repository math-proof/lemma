module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Def.v1.Atlas.NumberTheoryI.code.Cor2328
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Cor2328
public import Def.v1.Atlas.NumberTheoryI.code.TateCohomology.Part7


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

instance tateH0.finite_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Finite (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
  Finite.of_equiv _ (tateH0_equiv_pi_zmod n).symm

instance tateMinus1.finite_trivial_finFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Finite (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) := by
  haveI : Subsingleton (LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ)))) := by
    rw [ker_normMap_trivial_finFun n]; infer_instance
  haveI : Subsingleton (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
    Quotient.instSubsingletonQuotient _
  exact Finite.of_subsingleton

end TateCohomology
end
