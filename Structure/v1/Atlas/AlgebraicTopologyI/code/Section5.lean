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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part5
open CategoryTheory

universe u₀


namespace DeformationRetract

open unitInterval ContinuousMap

universe u

variable {X : Type u} [TopologicalSpace X]

/-- **Definition 5.8** (Deformation retract). An inclusion `A ↪ X` is a deformation
retract if there is a continuous map `h : X × I → X` such that `h(x, 0) = x`,
`h(x, 1) ∈ A` for all `x`, and `h(a, t) = a` for all `a ∈ A` and `t ∈ I`. This is
packaged as a retract `X → X` landing in `A` together with a relative homotopy from the
identity to the retract, fixing `A` pointwise. -/
structure IsDeformationRetract (A : Set X) where
  retract : C(X, X)
  retract_mem : ∀ x, retract x ∈ A
  homotopy : HomotopyRel (ContinuousMap.id X) retract A

end DeformationRetract
