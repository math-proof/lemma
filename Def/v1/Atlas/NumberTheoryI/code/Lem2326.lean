/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2326.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.GroupCohomology.Part9
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GroupCohomology
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro


noncomputable section

universe u

namespace GroupCohomology

open CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def homology_induced_H0_iso
    [DecidableEq G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupHomology A 0 :=
  groupHomology.indIso (⊥ : Subgroup G) A 0

end GroupCohomology
end
