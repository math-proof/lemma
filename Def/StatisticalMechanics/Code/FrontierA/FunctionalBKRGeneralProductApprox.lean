/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


def IsFiniteCoordinateSet (A : Set (∀ e, S e)) : Prop :=
  ∃ (n : E → ℕ) (q : ∀ e, S e → Fin (n e))
      (B : Set (∀ e, Fin (n e))),
    (∀ e, Measurable (q e)) ∧
      A = (fun x e => q e (x e)) ⁻¹' B

end StatMech.FrontierA
