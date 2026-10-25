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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section5
open CategoryTheory

universe u₀


namespace HomotopyEquivalence

open ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` is a homotopy equivalence (Definition 5.4) iff there
exists `g : Y → X` such that `g ∘ f ≃ idₓ` and `f ∘ g ≃ id_Y`. -/
def IsHomotopyEquiv (f : C(X, Y)) : Prop :=
  ∃ g : C(Y, X), (g.comp f).Homotopic (ContinuousMap.id X) ∧
    (f.comp g).Homotopic (ContinuousMap.id Y)

end HomotopyEquivalence
