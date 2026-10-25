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


namespace HomotopyTheory

open ContinuousMap unitInterval

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Definition 5.1** (Homotopy). A homotopy from `f₀` to `f₁` is a continuous map
`h : X × I → Y` satisfying `h(x, 0) = f₀(x)` and `h(x, 1) = f₁(x)`. Here it is realized
as the Mathlib datum `ContinuousMap.Homotopy f₀ f₁`. -/
def Homotopy (f₀ f₁ : C(X, Y)) : Type _ :=
  ContinuousMap.Homotopy f₀ f₁

/-- The proposition that `f₀` and `f₁` are homotopic, written `f₀ ≃ f₁` in the textbook
(Definition 5.1). -/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  ContinuousMap.Homotopic f₀ f₁

end HomotopyTheory
