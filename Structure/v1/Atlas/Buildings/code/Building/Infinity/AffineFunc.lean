/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part3
import Lemma.Fin.All_All_Any_And_InAndAll_In_Vertices
import Def.v1.Atlas.Buildings.code.Building.Infinity.AffineFunc
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- An *affine functional* on an apartment $A$: a function $V → ℝ$ which is affine
along the apartment's geodesic combinations. -/
structure AffineFunctional (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  toFun : V → ℝ
  affineComb : ℝ → V → V → V
  isAffine : ∀ (t : ℝ) (x y : V),
    (∃ s ∈ apartment.faces, x ∈ s) →
    (∃ s ∈ apartment.faces, y ∈ s) →
    toFun (affineComb t x y) = t * toFun x + (1 - t) * toFun y

/-- A *wall* $\eta$ in an apartment: the zero-set of an affine functional, together
with its two half-apartments $\eta^+, \eta^-$ and the axioms that the functional
is unbounded in any sector direction and has a definite sign on each sector. -/
structure Wall (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  functional : V → ℝ
  affineComb : ℝ → V → V → V
  functionalIsAffine : ∀ (t : ℝ) (x y : V),
    (∃ s ∈ apartment.faces, x ∈ s) →
    (∃ s ∈ apartment.faces, y ∈ s) →
    functional (affineComb t x y) = t * functional x + (1 - t) * functional y
  functional_vanishes : ∀ v ∈ vertices, functional v = 0
  halfPos : Set V
  halfNeg : Set V
  halfPos_def : ∀ v, (∃ s ∈ apartment.faces, v ∈ s) →
    (v ∈ halfPos ↔ 0 ≤ functional v)
  halfNeg_def : ∀ v, (∃ s ∈ apartment.faces, v ∈ s) →
    (v ∈ halfNeg ↔ functional v ≤ 0)
  halfPos_in_apartment : ∀ v ∈ halfPos, ∃ s ∈ apartment.faces, v ∈ s
  halfNeg_in_apartment : ∀ v ∈ halfNeg, ∃ s ∈ apartment.faces, v ∈ s
  functional_unbounded_on_sectors : ∀ (S : Sector b), S.apartment = apartment →
    ∀ M : ℝ, (∃ v ∈ S.vertices, functional v > M) ∨
             (∃ v ∈ S.vertices, functional v < -M)
  functional_definite_sign : ∀ (S : Sector b), S.apartment = apartment →
    ∀ (f : V → ℝ), (∀ v ∈ vertices, f v = 0) →
    (∀ v ∈ S.vertices, f S.baseVertex ≤ f v) ∨
    (∀ v ∈ S.vertices, f v ≤ f S.baseVertex)

/-- A *half-apartment*: a subset of an apartment equal to one of the canonical halves
$\eta^+$ or $\eta^-$ of some wall $\eta$. -/
structure HalfApartment (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  wall : Wall b
  wall_in_apartment : wall.apartment = apartment
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  is_canonical : vertices = wall.halfPos ∨ vertices = wall.halfNeg

end AffineBuilding
