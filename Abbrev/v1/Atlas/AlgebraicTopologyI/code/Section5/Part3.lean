/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
public import Mathlib.Algebra.Homology.AlternatingConst
public import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section5
@[expose] public section

open CategoryTheory

universe u₀


namespace HomotopyTheory

/-- **Definition 5.12** (Star-shaped). A subset `s ⊆ E` is star-shaped with respect to
`b ∈ s` if for every `x ∈ s` the segment `{tb + (1-t)x : t ∈ [0,1]}` lies in `s`.
Realized as Mathlib's `StarConvex ℝ b s`. -/
abbrev IsStarShaped {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (b : E) (s : Set E) : Prop :=
  StarConvex ℝ b s

end HomotopyTheory
