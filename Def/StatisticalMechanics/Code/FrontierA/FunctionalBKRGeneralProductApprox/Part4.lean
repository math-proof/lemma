/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Structure.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


universe w


noncomputable def finiteCoordinateSetData {A : Set (∀ e, S e)}
    (hA : IsFiniteCoordinateSet A) : FiniteCoordinateSetData A :=
  Classical.choice <| by
    rcases hA with ⟨n, q, B, hq, hAeq⟩
    exact ⟨
      { n := n
        q := q
        B := B
        measurable_q := hq
        eq_preimage := hAeq }⟩

noncomputable def finiteQuotientRepresentative
    [∀ e, Nonempty (S e)] {n : E → ℕ} (q : ∀ e, S e → Fin (n e))
    (e : E) (t : Fin (n e)) : S e := by
  classical
  exact if h : ∃ x, q e x = t then Classical.choose h else Classical.choice inferInstance

end StatMech.FrontierA
