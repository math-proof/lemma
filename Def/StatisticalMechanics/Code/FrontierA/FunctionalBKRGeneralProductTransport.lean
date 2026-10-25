/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part10
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


section DependentBlockExpectation

variable {D : E → Type*} [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
  [∀ e, Fintype (S e)] [∀ e, DecidableEq (S e)]


noncomputable def finitePiExpectation (w : ∀ e, S e → ℝ)
    (H : (∀ e, S e) → ℝ) : ℝ :=
  ∑ x, (∏ e, w e (x e)) * H x


noncomputable def finitePiDualExpectation (w : ∀ e, S e → ℝ)
    (H : ((∀ e, S e) × (∀ e, S e)) → ℝ) : ℝ :=
  finitePiExpectation w (fun x =>
    finitePiExpectation w (fun y => H (x, y)))

end DependentBlockExpectation
end StatMech.FrontierA
