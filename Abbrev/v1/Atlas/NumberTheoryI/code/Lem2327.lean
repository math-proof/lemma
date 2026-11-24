module
public import Def.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part9
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GroupCohomology
public import Mathlib.RepresentationTheory.FiniteIndex
public import Def.v1.Atlas.NumberTheoryI.code.Lem2327


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2327.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u

namespace GroupCohomology

open CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

abbrev indCoindIso_bot := @lemma_23_27

abbrev indCoindNatIso_bot := @lemma_23_27_natIso

end GroupCohomology
end
