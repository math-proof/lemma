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
public import Instance.v1.Atlas.NumberTheoryI.code.TateCohomology.Part2


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

def augInKerNorm (A : Rep k G) : Submodule k (LinearMap.ker (normMap k G A)) :=
  Submodule.comap (LinearMap.ker (normMap k G A)).subtype (augmentationSubmodule k G A)

def tateMinus1 (A : Rep k G) : Type u :=
  LinearMap.ker (normMap k G A) ⧸ augInKerNorm A

end TateCohomology
end
