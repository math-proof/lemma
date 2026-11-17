/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section8


public section

namespace AlgebraicTopologyI

open AlgebraicTopologyI

/-- A non-negatively graded chain complex: a sequence of abelian groups `X n` for `n : ℕ`
together with differentials `d : X (n + 1) →+ X n` satisfying `d ∘ d = 0`. This is the
form most naturally suited to the singular chain complex. -/
structure NatChainComplex where
  X : ℕ → Type*
  instAddCommGroup : ∀ n, AddCommGroup (X n)
  d : ∀ n, X (n + 1) →+ X n
  d_comp_d : ∀ n, (d n).comp (d (n + 1)) = 0

attribute [instance] NatChainComplex.instAddCommGroup

/-- The singular chain complex `S_*(X)` of a topological space `X`, packaged as a
`NatChainComplex`: in degree `n` the group is `SingularChains n X`, with differential
the singular boundary map. -/
structure NatChainComplex.Subcomplex (B : NatChainComplex) where
  toSubgroup : ∀ n, AddSubgroup (B.X n)
  d_maps : ∀ n (x : B.X (n + 1)), x ∈ toSubgroup (n + 1) → B.d n x ∈ toSubgroup n

end AlgebraicTopologyI
