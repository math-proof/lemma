/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentTightness
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem boundaryCurrentMeasure_sources_interior (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G))
      {m | (sources G (ofEdgeFun G m)) ∩ interior = ∅} = 1 := by
  change (boundaryCurrentPMF G beta J hbeta hJ interior).toMeasure
    {m | (sources G (ofEdgeFun G m)) ∩ interior = ∅} = 1
  apply (PMF.toMeasure_apply_eq_one_iff _ (Set.to_countable _).measurableSet).2
  intro m hm
  by_contra hsrc
  have hmne : boundaryCurrentPMF G beta J hbeta hJ interior m ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hm
  apply hmne
  rw [boundaryCurrentPMF_apply]
  have hsrc' : (sources G (ofEdgeFun G m)) ∩ interior ≠ ∅ := by
    simpa using hsrc
  simp [boundaryCurrentRawMass, hsrc']

end StatMech.FrontierB
