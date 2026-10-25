/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
open scoped Classical

variable {V : Type*} [DecidableEq V]


/-- A *folding* of a chamber complex $X$: an idempotent simplicial endomorphism that maps
chambers to chambers and facets to facets, is not the identity, is two-to-one on its fixed
half-apartment, has a boundary edge (a fixed chamber adjacent to a moved one), and along any
gallery between two fixed chambers any "moved" chamber forces an exit edge from the fixed
half. Also requires `stutter_at_boundary`: a moved chamber adjacent to a fixed one is mapped to
that fixed chamber. The final clause excludes stutters in minimal galleries between fixed
chambers. -/
structure Folding (X : ChamberComplex V) where
  morph : SimplicialComplex.Morphism X.toSimplicialComplex X.toSimplicialComplex
  chamberMap : morph.IsChamberMap
  preservesFacets : morph.PreservesFacets
  idempotent : ∀ v, morph.toFun (morph.toFun v) = morph.toFun v
  not_id : ∃ C, X.toSimplicialComplex.IsMaximal C ∧ C.image morph.toFun ≠ C
  twoToOne : ∀ C, X.toSimplicialComplex.IsMaximal C →
    C.image morph.toFun = C →
    ∃! D, X.toSimplicialComplex.IsMaximal D ∧ D ≠ C ∧ D.image morph.toFun = C
  exists_boundary : ∃ C D, X.toSimplicialComplex.Adjacent C D ∧
    C.image morph.toFun = C ∧ D.image morph.toFun ≠ D
  gallery_exits :
    ∀ (C D : Finset V),
      X.toSimplicialComplex.IsMaximal C → C.image morph.toFun = C →
      X.toSimplicialComplex.IsMaximal D → D.image morph.toFun = D →
      ∀ (g : Gallery X.toSimplicialComplex), g.Connects C D →
      ∀ (E : Finset V), E ∈ g.chambers → E.image morph.toFun ≠ E →
      ∃ Ci Ci1, Ci ∈ g.chambers ∧ Ci1 ∈ g.chambers ∧
        X.toSimplicialComplex.Adjacent Ci Ci1 ∧
        (X.toSimplicialComplex.IsMaximal Ci ∧ Ci.image morph.toFun = Ci) ∧
        ¬(X.toSimplicialComplex.IsMaximal Ci1 ∧ Ci1.image morph.toFun = Ci1)
  stutter_at_boundary :
    ∀ (Ci Ci1 : Finset V),
      X.toSimplicialComplex.Adjacent Ci Ci1 →
      (X.toSimplicialComplex.IsMaximal Ci ∧ Ci.image morph.toFun = Ci) →
      Ci1.image morph.toFun ≠ Ci1 →
      Ci1.image morph.toFun = Ci
  stutter_contradicts_minimality :
    ∀ (C D : Finset V),
      X.toSimplicialComplex.IsMaximal C → C.image morph.toFun = C →
      X.toSimplicialComplex.IsMaximal D → D.image morph.toFun = D →
      ∀ (g : Gallery X.toSimplicialComplex), g.Connects C D →
      g.length = galleryDist X.toSimplicialComplex C D →
      ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers →
        X.toSimplicialComplex.Adjacent Ci Ci1 →
        Ci1.image morph.toFun = Ci.image morph.toFun → False

