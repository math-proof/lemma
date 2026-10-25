/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8


namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

attribute [instance] IntChainComplex.instAddCommGroup

/-- The `n`th relative homology of a chain complex `B` modulo a subcomplex `A`, defined
as the homology of the quotient complex `B / A`. This is the abstract algebraic
version of the relative homology of Definition 8.6. -/
noncomputable def RelativeHomology (n : ℤ) (B : IntChainComplex) (A : B.Subcomplex) :=
  (A.quotientComplex B).homologyGroup n

end ExactSequence

namespace AlgebraicTopologyI

open AlgebraicTopologyI

/-- Push a singular `n`-simplex of the subspace `A ⊆ X` forward along the inclusion
`A ↪ X` to obtain a singular `n`-simplex of `X`. -/
def singularSimplexInclusion (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    SingularSimplex n ↥A → SingularSimplex n X :=
  fun σ => ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ σ

/-- The inclusion of singular chain groups `S_n(A) →+ S_n(X)` induced by the inclusion
`A ↪ X`, obtained by freely extending `singularSimplexInclusion`. -/
def singularChainsInclusion (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    SingularChains n ↥A →+ SingularChains n X :=
  FreeAbelianGroup.map (singularSimplexInclusion n X A)

/-- The relative singular `n`-chains `S_n(X, A) = S_n(X) / S_n(A)`, defined by quotienting
the singular chains of `X` by the image of the inclusion from the singular chains
of `A`. This is the underlying group of Definition 8.5 in a single degree. -/
def RelativeSingularChains (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :=
  SingularChains n X ⧸ (singularChainsInclusion n X A).range

end AlgebraicTopologyI
