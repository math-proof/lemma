/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Module.Prod
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section11.Part4

@[expose] public section

open Set Topology

universe u

variable {X : Type*} [TopologicalSpace X]


/-- **Definition 11.2 (Cover).** A family `𝒜` of subsets of a topological space `X` is a
*cover* if the union of the interiors of its members equals all of `X`. -/
def IsCover (𝒜 : Set (Set X)) : Prop :=
  ⋃₀ (interior '' 𝒜) = Set.univ

/-- **Definition 11.3 (𝒜-small simplex).** Given a cover `𝒜` of `X`, a singular `n`-simplex
`σ : Δⁿ → X` is *𝒜-small* if its image lies entirely in some `A ∈ 𝒜`. -/
def IsSmall {n : ℕ} (𝒜 : Set (Set X)) (σ : SingularSimplex n X) : Prop :=
  ∃ A ∈ 𝒜, Set.range (show C(↥(stdSimplex ℝ (Fin (n + 1))), X) from σ) ⊆ A

