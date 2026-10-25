/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Prod
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section11.Part2
open Set Topology

universe u


namespace EilenbergSteenrod

attribute [instance] TopPair.instTop

/-- The identity morphism on a pair `(X, A)`. -/
def MapOfPairs.id (P : TopPair) : MapOfPairs P P where
  toFun := _root_.id
  continuous_toFun := continuous_id
  mapsTo := fun _ h => h

/-- Composition of morphisms of pairs. -/
def MapOfPairs.comp {P Q R : TopPair} (g : MapOfPairs Q R) (f : MapOfPairs P Q) :
    MapOfPairs P R where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  mapsTo := g.mapsTo.comp f.mapsTo

/-- The restriction of a map of pairs `f : (X, A) → (Y, B)` to the subspaces, producing
`f|_A : (A, ∅) → (B, ∅)`. Used to express naturality of the boundary map. -/
def MapOfPairs.restrictToSub {P Q : TopPair} (f : MapOfPairs P Q) :
    MapOfPairs P.subPair Q.subPair where
  toFun := fun a => ⟨f.toFun a.val, f.mapsTo a.property⟩
  continuous_toFun := Continuous.subtype_mk (f.continuous_toFun.comp continuous_subtype_val) _
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(A, ∅) ↪ (X, ∅)` arising from the subspace inclusion `A ⊆ X`.
This is the map `i` in the relative homology long exact sequence. -/
def inclusionSubToSpace (P : TopPair) : MapOfPairs P.subPair (TopPair.ofSpace P.space) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h => h.elim

/-- The map of pairs `(X, ∅) → (X, A)` given by the identity on `X`. This is the
quotient-type map `j` in the relative long exact sequence. -/
def inclusionSpaceToPair (P : TopPair) : MapOfPairs (TopPair.ofSpace P.space) P where
  toFun := _root_.id
  continuous_toFun := continuous_id
  mapsTo := fun _ h => h.elim

/-- The excision inclusion of pairs `(X − U, A − U) ↪ (X, A)`. The excision axiom asserts
this map induces an isomorphism in homology whenever the triple `(X, A, U)` is excisive. -/
def excisionInclusion (P : TopPair) (U : Set P.space) :
    MapOfPairs (P.excisePair U) P where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun ⟨_, _⟩ hx => hx

/-- The inclusion of the `i`-th summand `Xᵢ ↪ ∐ⱼ Xⱼ` of a coproduct of spaces, as a map of
pairs. These maps assemble into the Milnor (coproduct) axiom isomorphism. -/
def coproductInclusion (ι : Type u) (X : ι → Type u) [∀ j, TopologicalSpace (X j)] (i : ι) :
    MapOfPairs (TopPair.ofSpace (X i)) (TopPair.coproduct ι X) where
  toFun := Sigma.mk i
  continuous_toFun := continuous_sigmaMk
  mapsTo := fun _ h => h.elim

end EilenbergSteenrod
