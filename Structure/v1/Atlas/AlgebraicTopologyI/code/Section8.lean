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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section8


namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- A short exact sequence `0 → A → B → C → 0` of abelian groups, packaged as the
injectivity of `i`, the surjectivity of `p`, and exactness at the middle term `B`.
This realizes Definition 8.3. -/
structure IsShortExact (i : A →+ B) (p : B →+ C) : Prop where
  injective : Function.Injective i
  surjective : Function.Surjective p
  exact : Function.Exact i p

/-- A chain complex indexed by the integers: a sequence of abelian groups `X n` together
with differentials `d : X n →+ X (n - 1)` satisfying `d ∘ d = 0`. This is the structure
underlying Definition 1.6, used here as the ambient setting for relative chain complexes. -/
structure IntChainComplex where
  X : ℤ → Type*
  instAddCommGroup : ∀ n, AddCommGroup (X n)
  d : ∀ n, X n →+ X (n - 1)
  d_comp_d : ∀ n, (d (n - 1)).comp (d n) = 0

attribute [instance] IntChainComplex.instAddCommGroup

/-- A subcomplex of an integer-indexed chain complex `B`: a choice of subgroup in each
degree that is closed under the differential `d`. This is the input data for
forming the quotient chain complex in Lemma 8.4. -/
structure IntChainComplex.Subcomplex (B : IntChainComplex) where
  toSubgroup : ∀ n, AddSubgroup (B.X n)
  d_maps : ∀ n (x : B.X n), x ∈ toSubgroup n → B.d n x ∈ toSubgroup (n - 1)

/-- A chain map between integer-indexed chain complexes: a family of group homomorphisms
commuting with the differentials in each degree. -/
structure IntChainMap (B C : IntChainComplex) where
  f : ∀ n, B.X n →+ C.X n
  comm : ∀ n, (C.d n).comp (f n) = (f (n - 1)).comp (B.d n)

end ExactSequence
