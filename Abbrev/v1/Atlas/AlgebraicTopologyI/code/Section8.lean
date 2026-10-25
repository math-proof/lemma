/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section8


namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- Exactness at the middle term of `A →+ B →+ C`: the image of `f` equals the kernel of `g`.
This formalizes the equality `im f = ker g` from Definition 8.1 by reusing Mathlib's
`Function.Exact`. -/
abbrev exactAt (f : A →+ B) (g : B →+ C) : Prop := Function.Exact f g

end ExactSequence
