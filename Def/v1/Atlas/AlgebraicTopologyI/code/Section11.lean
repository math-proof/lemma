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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section11
open Set Topology

universe u


namespace EilenbergSteenrod

attribute [instance] TopPair.instTop

/-- The pair `(X, ∅)` associated with a topological space `X`, viewing an absolute space
as a relative one with empty subspace. -/
def TopPair.ofSpace (X : Type u) [TopologicalSpace X] : TopPair := ⟨X, ‹_›, ∅⟩

/-- The pair `(A, ∅)` obtained by regarding the subspace `A` of a pair `P = (X, A)` as
a standalone space. This is used to express the boundary map `Hₙ(X, A) → Hₙ₋₁(A)`. -/
def TopPair.subPair (P : TopPair) : TopPair := TopPair.ofSpace P.sub

/-- The one-point pair `(*, ∅)`, used as the test object for the dimension axiom of a
homology theory. -/
def TopPair.point : TopPair.{u} := TopPair.ofSpace PUnit.{u + 1}

/-- Given a pair `P = (X, A)` and a subset `U ⊆ X`, the excised pair `(X − U, A − U)`. This
is the source of the excision inclusion `(X − U, A − U) ↪ (X, A)`. -/
def TopPair.excisePair (P : TopPair) (U : Set P.space) : TopPair where
  space := (Uᶜ : Set P.space)
  instTop := instTopologicalSpaceSubtype
  sub := Subtype.val ⁻¹' P.sub

/-- The pair `(∐ᵢ Xᵢ, ∅)` formed by the disjoint union of a family of spaces, used to state
the Milnor (coproduct) axiom of a homology theory. -/
def TopPair.coproduct (ι : Type u) (X : ι → Type u) [∀ i, TopologicalSpace (X i)] :
    TopPair := TopPair.ofSpace (Σ i, X i)

end EilenbergSteenrod
