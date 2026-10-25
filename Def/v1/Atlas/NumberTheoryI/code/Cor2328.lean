/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor2328.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Lem2326
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lem2326
import Abbrev.v1.Atlas.NumberTheoryI.code.Lem2327


noncomputable section

universe u

namespace GroupCohomology

open CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

def corollary_23_28_homology_ind_H0_iso [DecidableEq G] [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupHomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupHomology A 0 :=
  homology_induced_H0_iso A

def corollary_23_28_cohomology_coind_H0_iso [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupCohomology A 0 :=
  cohomology_coinduced_H0_iso A

def corollary_23_28_cohomology_ind_H0_iso [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupCohomology (Rep.ind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupCohomology A 0 := by
  classical
  exact (groupCohomology.functor k G 0).mapIso (lemma_23_27 A) ≪≫
    cohomology_coinduced_H0_iso A

def corollary_23_28_homology_coind_H0_iso [DecidableEq G] [Fintype G]
    (A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)) :
    groupHomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) 0 ≅
    groupHomology A 0 := by
  classical
  exact (groupHomology.functor k G 0).mapIso (lemma_23_27 A).symm ≪≫
    homology_induced_H0_iso A

end GroupCohomology
end
