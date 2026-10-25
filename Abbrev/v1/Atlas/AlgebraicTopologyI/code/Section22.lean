/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Module.Projective
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.FundamentalThm


namespace ProjectiveModules

/-- **Definition 22.2 (Projective module).**  An `R`-module `P` is
*projective* if it satisfies the lifting property: every surjection
`f : M → N` and every map `g : P → N` admit a lift `h : P → M` with
`f ∘ h = g`.  Equivalently, `P` is a direct summand of a free module.
Thin wrapper around Mathlib's `Module.Projective`. -/
abbrev IsProjectiveModule (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P]
    [Module R P] : Prop :=
  Module.Projective R P

end ProjectiveModules
