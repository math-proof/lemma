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
public import Instance.v1.Atlas.NumberTheoryI.code.TateCohomology


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

def normImageInInvariants (A : Rep k G) : Submodule k A.ρ.invariants :=
  Submodule.comap A.ρ.invariants.subtype (LinearMap.range (normMap k G A))

def tateH0 (A : Rep k G) : Type u :=
  A.ρ.invariants ⧸ normImageInInvariants A

end TateCohomology
end
