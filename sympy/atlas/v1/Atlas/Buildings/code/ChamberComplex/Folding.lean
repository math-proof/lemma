/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Basic
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness

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

variable {X : ChamberComplex V}

namespace Folding

/-- The set of chambers fixed (as sets) by the folding $f$, i.e. $f(C) = C$. -/
def fixedChambers (f : Folding X) : Set (Finset V) :=
  {C | X.toSimplicialComplex.IsMaximal C ∧ C.image f.morph.toFun = C}

/-- The set of chambers moved by the folding $f$, i.e. $f(C) \neq C$. -/
def movedChambers (f : Folding X) : Set (Finset V) :=
  {C | X.toSimplicialComplex.IsMaximal C ∧ C.image f.morph.toFun ≠ C}

/-- A *reversible folding* is a pair $(f, g)$ of foldings such that $f$'s fixed chambers equal
$g$'s moved chambers (and vice versa), and the two foldings exchange the two boundary chambers
of any wall: $g(C) = C'$ where $C, C'$ are an adjacent fixed/moved pair under $f$. -/
structure ReversibleFolding (X : ChamberComplex V) where
  f : Folding X
  g : Folding X
  complementary_fixed : f.fixedChambers = g.movedChambers
  complementary_moved : f.movedChambers = g.fixedChambers
  opposite_action : ∀ C C',
    X.toSimplicialComplex.IsMaximal C →
    X.toSimplicialComplex.IsMaximal C' →
    C ≠ C' → C.image f.morph.toFun = C → C'.image f.morph.toFun = C →
    C.image g.morph.toFun = C'
  opposite_action' : ∀ C C',
    X.toSimplicialComplex.IsMaximal C →
    X.toSimplicialComplex.IsMaximal C' →
    C ≠ C' → C.image g.morph.toFun = C → C'.image g.morph.toFun = C →
    C.image f.morph.toFun = C'

namespace ReversibleFolding

variable (rf : ReversibleFolding X)

/-- The *wall* of a folding $f$: faces fixed pointwise by $f$ that lie in some moved chamber. -/
def Wall (X : ChamberComplex V) (f : Folding X) : Set (Finset V) :=
  {x | x ∈ X.toSimplicialComplex.faces ∧
       (∀ v ∈ x, f.morph.toFun v = v) ∧
       (∃ C, X.toSimplicialComplex.IsMaximal C ∧
              C.image f.morph.toFun ≠ C ∧ x ⊆ C)}

/-- The vertex-level reflection associated with a reversible folding: at each vertex, apply $g$
where $f$ fixes, and $f$ elsewhere. -/
def reflectionFun (rf : ReversibleFolding X) : V → V :=
  fun v => if rf.f.morph.toFun v = v then rf.g.morph.toFun v
           else rf.f.morph.toFun v

/-- Two chambers lie on *opposite* sides of the wall of $f$: one is fixed and the other moved. -/
def OppositeSides (f : Folding X) (C D : Finset V) : Prop :=
  (C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∨
  (D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C)

/-- Two chambers lie on the *same* side of the wall of $f$: both fixed or both moved. -/
def SameSide (f : Folding X) (C D : Finset V) : Prop :=
  (C.image f.morph.toFun = C ∧ D.image f.morph.toFun = D) ∨
  (C.image f.morph.toFun ≠ C ∧ D.image f.morph.toFun ≠ D)

/-- A *wall reflection*: a reversible folding equipped with the cross-fixing and cover axioms
needed to make its associated reflection a well-defined involution. -/
structure WallReflection (X : ChamberComplex V) where
  rf : ReversibleFolding X
  fg_id : ∀ v, rf.f.morph.toFun v = v → rf.f.morph.toFun (rf.g.morph.toFun v) = v
  gf_id : ∀ v, rf.g.morph.toFun v = v → rf.g.morph.toFun (rf.f.morph.toFun v) = v
  cover : ∀ v, rf.f.morph.toFun v = v ∨ rf.g.morph.toFun v = v

namespace WallReflection

variable (s : WallReflection X)

/-- The reflection map of a wall reflection. -/
def refl : V → V := reflectionFun s.rf

/-- The wall (fixed set) of a wall reflection, viewed as a set of faces. -/
def wall : Set (Finset V) := Wall X s.rf.f
