/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/SphericalFiniteDiameter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Spherical
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.List.Any.of.Not.In_A.IsChainA
import Lemma.Finset.OppositeSides.of.EqToSimplicialComplex.AreOppositeToSimplicialComplexToChamberComplex.IsMaximal.IsMaximal.In_Faces.In_Faces.In_Apartments.OppositeChamberHyp
import sympy.atlas.v1.Atlas.Buildings.code.Building.Convexity
import sympy.atlas.v1.Atlas.Buildings.code.Building.OppositeChambers
import Lemma.Finset.Adjacent.of.Adjacent
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Data.Set.Finite.List

variable {V : Type*} [DecidableEq V]

/-- A simplicial complex has *finite diameter* bounded by $d$ if every pair
of chambers has gallery distance at most $d$. -/
def SimplicialComplex.HasFiniteDiameter (K : SimplicialComplex V) (d : ℕ) : Prop :=
  ∀ C D, K.IsMaximal C → K.IsMaximal D → galleryDist K C D ≤ d

/-- A building has *finite diameter* if its underlying chamber complex does. -/
def Building.HasFiniteDiameter (b : Building V) (d : ℕ) : Prop :=
  b.toChamberComplex.toSimplicialComplex.HasFiniteDiameter d

/-- Bundle of hypotheses needed for the opposite-chamber theorem in the
generic apartment-system setting: reversibility, distance equality, fold
decreases distance, maximality preservation, additivity, and existence of
galleries through chambers. -/
structure OppositeChamberHypGen {V : Type*} [DecidableEq V]
    (K : ChamberComplex V) (𝒜 : ApartmentSystem K) where
  apt_reversible_foldings :
    ∀ A ∈ 𝒜.apartments,
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
    ∀ A ∈ 𝒜.apartments,
      ∀ C D : Finset V,
        C ∈ A.faces → D ∈ A.faces →
        A.IsMaximal C → A.IsMaximal D →
        galleryDist A C D = galleryDist K.toSimplicialComplex C D
  fold_decreases_dist :
    ∀ A ∈ 𝒜.apartments,
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
    ∀ A ∈ 𝒜.apartments,
      ∀ (cc : ChamberComplex V),
        cc.toSimplicialComplex = A →
        ∀ (f : ChamberComplex.Folding cc),
          ∀ D : Finset V,
            cc.toSimplicialComplex.IsMaximal D →
            cc.toSimplicialComplex.IsMaximal (D.image f.morph.toFun)
  wall_sep_additive_dist :
    ∀ A ∈ 𝒜.apartments,
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
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal C' →
      K.toSimplicialComplex.IsMaximal D →
      galleryDist K.toSimplicialComplex C D =
        galleryDist K.toSimplicialComplex C C' +
        galleryDist K.toSimplicialComplex C' D →
      ∃ (g : Gallery K.toSimplicialComplex),
        g.Connects C D ∧
        g.length = galleryDist K.toSimplicialComplex C D ∧
        C' ∈ g.chambers
