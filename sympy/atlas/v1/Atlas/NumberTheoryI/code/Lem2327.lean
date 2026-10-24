/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem2327.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.GroupCohomology
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GroupCohomology
import Mathlib.RepresentationTheory.FiniteIndex

noncomputable section

universe u

namespace GroupCohomology

open CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def lemma_23_27 [Fintype G] (A : Rep.{u} k ↥(⊥ : Subgroup G)) :
    Rep.ind (⊥ : Subgroup G).subtype A ≅
    Rep.coind (⊥ : Subgroup G).subtype A := by
  classical
  exact Rep.indCoindIso A

def lemma_23_27_natIso [Fintype G] :
    induced_def k G ≅ coinduced_def k G := by
  classical
  exact Rep.indCoindNatIso k (⊥ : Subgroup G)

abbrev indCoindIso_bot := @lemma_23_27

abbrev indCoindNatIso_bot := @lemma_23_27_natIso

end GroupCohomology
