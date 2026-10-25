/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Uniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Structure.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness
open scoped Classical

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace SimplicialComplex

/-- A morphism is a *chamber map* if it sends maximal faces to maximal faces. -/
def Morphism.IsChamberMap {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f : Morphism K L) : Prop :=
  ∀ C, K.IsMaximal C → L.IsMaximal (C.image f.toFun)

/-- A morphism *preserves facets* if codim-$1$ inclusions in $K$ go to codim-$1$ inclusions in $L$. -/
def Morphism.PreservesFacets {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f : Morphism K L) : Prop :=
  ∀ F C, K.IsFacet F C → L.IsFacet (F.image f.toFun) (C.image f.toFun)

/-- Two morphisms `f, g` *agree on $C$* if they coincide on every vertex of $C$. -/
def AgreeOn {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f g : Morphism K L) (C : Finset V) : Prop :=
  ∀ v ∈ C, f.toFun v = g.toFun v

/-- Two morphisms have *equal image on $C$*: $f(C) = g(C)$ as sets. -/
def AgreeOnImage {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f g : Morphism K L) (C : Finset V) : Prop :=
  C.image f.toFun = C.image g.toFun

/-- The "at most two chambers per facet" property: a facet $F$ lies in at most two chambers. -/
def AtMostTwoChambers (L : SimplicialComplex W) : Prop :=
  ∀ F C D E, L.IsFacet F C → L.IsMaximal C →
    L.IsFacet F D → L.IsMaximal D → D ≠ C →
    L.IsFacet F E → L.IsMaximal E → E ≠ C →
    D = E

/-- A morphism is *non-stuttering on adjacent pairs*: it never collapses adjacent chambers. -/
def Morphism.NonStutteringAdj {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f : Morphism K L) : Prop :=
  ∀ C D, K.Adjacent C D → C.image f.toFun ≠ D.image f.toFun

/-- *Sub-face compatibility*: if $f, g$ agree on the image of a chamber $C$, then they agree on
the image of any face of $C$. -/
def SubFaceCompatible {K : SimplicialComplex V} {L : SimplicialComplex W}
    (f g : Morphism K L) : Prop :=
  ∀ C, K.IsMaximal C → AgreeOnImage f g C →
    ∀ F, K.IsFace F C → AgreeOnImage f g F

/-- The image gallery $(C \mapsto f(C))$ stutters: some adjacent images are equal. -/
def GalleryStuttersUnder (cs : List (Finset V)) (f : V → V) : Prop :=
  ¬ List.IsChain (· ≠ ·) (cs.map (fun C => C.image f))

/-- $f$ fixes every chamber of $cs$ pointwise. -/
def FixesAllPointwise (cs : List (Finset V)) (f : V → V) : Prop :=
  ∀ C ∈ cs, ∀ v ∈ C, f v = v

end SimplicialComplex
