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


noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

abbrev GModule (k : Type u) [CommRing k] (G : Type u) [Group G] := Rep k G

abbrev GInvariants (A : Rep k G) : Submodule k A := A.ρ.invariants

abbrev nCochains (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (groupCohomology.inhomogeneousCochains A).X n

abbrev coboundaryMap (A : Rep k G) (n : ℕ) :
    nCochains A n ⟶ nCochains A (n + 1) :=
  (groupCohomology.inhomogeneousCochains A).d n (n + 1)

abbrev cochainComplex (A : Rep k G) : CochainComplex (ModuleCat k) ℕ :=
  groupCohomology.inhomogeneousCochains A

abbrev nCocycles (A : Rep k G) (n : ℕ) : ModuleCat k :=
  groupCohomology.cocycles A n

abbrev CohomologyGroup (A : Rep k G) (n : ℕ) : ModuleCat k :=
  groupCohomology A n

end GroupCohomology
end
