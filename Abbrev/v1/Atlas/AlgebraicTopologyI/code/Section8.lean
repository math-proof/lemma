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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section8

@[expose] public section


namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Exactness at the middle term of `A →+ B →+ C`: the image of `f` equals the kernel of `g`.
This formalizes the equality `im f = ker g` from Definition 8.1 by reusing Mathlib's
`Function.Exact`. -/
abbrev exactAt (f : A →+ B) (g : B →+ C) : Prop := Function.Exact f g

end ExactSequence
