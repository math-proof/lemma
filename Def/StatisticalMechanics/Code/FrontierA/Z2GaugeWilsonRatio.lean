/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonRatio.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeElitzur.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


noncomputable def gaugeClosedSurfaceSum (incidence : P -> Finset E)
    (K : P -> ℝ) : ℝ := by
  classical
  exact ∑ A ∈ (Finset.univ : Finset P).powerset.filter
    (IsClosedPlaquetteSet incidence), ∏ p ∈ A, Real.tanh (K p)


noncomputable def gaugeWilsonSurfaceSum (incidence : P -> Finset E)
    (K : P -> ℝ) (L : Finset E) : ℝ := by
  classical
  exact ∑ A ∈ (Finset.univ : Finset P).powerset.filter
    (fun A => HasWilsonBoundary incidence A L), ∏ p ∈ A, Real.tanh (K p)

end StatMech.FrontierA
