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

@[expose] public section

namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- A pair of consecutive group homomorphisms `f`, `g` forms a complex when `g ∘ f = 0`,
i.e. the image of `f` is contained in the kernel of `g`. This is the "complex" half of
Definition 8.1's notion of an exact sequence: a sequence whose composites all vanish. -/
def isComplex (f : A →+ B) (g : B →+ C) : Prop := ∀ a, g (f a) = 0

end ExactSequence
