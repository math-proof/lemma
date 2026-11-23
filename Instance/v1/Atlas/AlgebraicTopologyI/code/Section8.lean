/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section8.Part2
@[expose] public section

namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

attribute [instance] IntChainComplex.instAddCommGroup

/-- The homology group inherits an abelian group structure from the quotient construction. -/
noncomputable instance IntChainComplex.instAddCommGroupHomology
    (C : IntChainComplex) (n : ℤ) : AddCommGroup (C.homologyGroup n) :=
  QuotientAddGroup.Quotient.addCommGroup _

end ExactSequence
