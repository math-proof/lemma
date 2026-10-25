/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Homology.AlternatingConst
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section5
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
