/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Lemma.Finset.Adjacent
import Lemma.Nat.NotChamberAdjacent
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Mathlib.Order.Zorn
import Def.v1.Atlas.Buildings.code.Building.Basic
set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]


/-- An apartment system on a chamber complex $K$: a collection of "apartments" subject to the
axioms (B1)–(B3) of buildings: every two chambers lie in a common apartment, common-chamber
apartments admit a fixing simplicial isomorphism, gallery-convexity inside apartments, plus
the Coxeter-complex structure on each apartment. -/
structure ApartmentSystem (K : ChamberComplex V) where
  apartments : Set (SimplicialComplex V)
  nonempty_apartments : ∃ A, A ∈ apartments
  sub : ∀ A ∈ apartments, IsSubcomplex A K.toSimplicialComplex
  contains_pair : ∀ C D,
    K.toSimplicialComplex.IsMaximal C →
    K.toSimplicialComplex.IsMaximal D →
    ∃ A ∈ apartments, C ∈ A.faces ∧ D ∈ A.faces
  iso_exists : ∀ A ∈ apartments, ∀ A' ∈ apartments,
    ∀ x, x ∈ A.faces → x ∈ A'.faces →
    ∀ C, A.IsMaximal C → C ∈ A'.faces →
    ∃ φ : SimplicialMap A A',
      (∀ v ∈ x, φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v)
  maximal_in_apt_is_maximal :
    ∀ A ∈ apartments, ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal C
  gallery_convex :
    ∀ A ∈ apartments, ∀ C D : Finset V,
      C ∈ A.faces → K.toSimplicialComplex.IsMaximal C →
      D ∈ A.faces → K.toSimplicialComplex.IsMaximal D →
      ∀ g : Gallery K.toSimplicialComplex,
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        ∀ E ∈ g.chambers, E ∈ A.faces
  building_maximal_in_apt_is_apt_maximal :
    ∀ A ∈ apartments, ∀ C, C ∈ A.faces →
      K.toSimplicialComplex.IsMaximal C → A.IsMaximal C
  apt_nonempty :
    ∀ A ∈ apartments, ∃ s, s ∈ A.faces
  iso_bijective : ∀ A ∈ apartments, ∀ A' ∈ apartments,
    ∀ C, C ∈ A.faces → C ∈ A'.faces → A.IsMaximal C →
    ∃ φ : V → V, Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
  apt_is_coxeter : ∀ A ∈ apartments,
    ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → M.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
        cc.IsThin

/-- When $\varphi$ is constant on its domain $S_1$, every element of $S_1$ is itself maximal in $K$. -/
structure Building (V : Type*) [DecidableEq V] extends ChamberComplex V where
  apartmentSystem : ApartmentSystem toChamberComplex
  thick : toChamberComplex.IsThick

