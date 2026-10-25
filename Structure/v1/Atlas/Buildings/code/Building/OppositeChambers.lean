/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/OppositeChambers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Spherical
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
open scoped Classical

variable {V : Type*} [DecidableEq V]


/-- Hypothesis bundle for the opposite-chamber theorem: collects the
ingredients about reversible foldings, distance equality between apartment
and building, fold-decreasing distance, fold-preserved maximality, additive
wall-separation distances, and the existence of galleries passing through a
chosen chamber. -/
structure OppositeChamberHyp (b : Building V) where
  apt_reversible_foldings :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∃ (f' : ChamberComplex.Folding cc),
            (∀ D : Finset V, cc.toSimplicialComplex.IsMaximal D →
              (D.image f.morph.toFun = D ↔ D.image f'.morph.toFun ≠ D)) ∧
            (∀ D : Finset V, cc.toSimplicialComplex.IsMaximal D →
              D.image f.morph.toFun = D →
              (D.image f'.morph.toFun).image f.morph.toFun = D)
  apt_dist_eq :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ C D : Finset V,
        C ∈ A.faces → D ∈ A.faces →
        A.IsMaximal C → A.IsMaximal D →
        galleryDist A C D =
          galleryDist b.toChamberComplex.toSimplicialComplex C D
  fold_decreases_dist :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ C D : Finset V,
            cc.toSimplicialComplex.IsMaximal C →
            cc.toSimplicialComplex.IsMaximal D →
            C.image f.morph.toFun = C →
            D.image f.morph.toFun ≠ D →
            galleryDist cc.toSimplicialComplex C (D.image f.morph.toFun) <
              galleryDist cc.toSimplicialComplex C D
  fold_preserves_maximal :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ D : Finset V,
            cc.toSimplicialComplex.IsMaximal D →
            cc.toSimplicialComplex.IsMaximal (D.image f.morph.toFun)
  wall_sep_additive_dist :
    ∀ A ∈ b.apartmentSystem.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ C D C' : Finset V,
          cc.toSimplicialComplex.IsMaximal C →
          cc.toSimplicialComplex.IsMaximal D →
          cc.toSimplicialComplex.IsMaximal C' →
          (∀ (f : ChamberComplex.Folding cc),
            ChamberComplex.OppositeSides f C D) →
          galleryDist cc.toSimplicialComplex C D =
            galleryDist cc.toSimplicialComplex C C' +
            galleryDist cc.toSimplicialComplex C' D
  gallery_through_chamber :
    ∀ C C' D : Finset V,
      b.toChamberComplex.toSimplicialComplex.IsMaximal C →
      b.toChamberComplex.toSimplicialComplex.IsMaximal C' →
      b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      galleryDist b.toChamberComplex.toSimplicialComplex C D =
        galleryDist b.toChamberComplex.toSimplicialComplex C C' +
        galleryDist b.toChamberComplex.toSimplicialComplex C' D →
      ∃ (g : Gallery b.toChamberComplex.toSimplicialComplex),
        g.Connects C D ∧
        g.length = galleryDist b.toChamberComplex.toSimplicialComplex C D ∧
        C' ∈ g.chambers

