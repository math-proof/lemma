/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Def.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part7


noncomputable section

open CategoryTheory

universe u

namespace ChainHomotopy

open CategoryTheory

universe v

variable {R : Type v} [Ring R]

abbrev CochainComplexRMod (R : Type v) [Ring R] := CochainComplex (ModuleCat.{v} R) ℕ

abbrev cochainObject (C : CochainComplexRMod R) (n : ℕ) : ModuleCat R := C.X n

abbrev coboundaryMap (C : CochainComplexRMod R) (n : ℕ) :
    cochainObject C n ⟶ cochainObject C (n + 1) :=
  C.d n (n + 1)

abbrev cochainCohomology (C : CochainComplexRMod R) (n : ℕ) : ModuleCat R := C.homology n

end ChainHomotopy
end
