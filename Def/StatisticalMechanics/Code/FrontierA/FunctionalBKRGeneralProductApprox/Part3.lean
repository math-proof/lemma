/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part3
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


def PiSetDependsOn (K : Set E) (A : Set (∀ e, S e)) : Prop :=
  ∀ ⦃x y⦄, piAgreeOn K x y → (x ∈ A ↔ y ∈ A)

end StatMech.FrontierA
