/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part8
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


open MeasureTheory Filter

lemma measurable_intervalStatePattern (r : ℕ) : Measurable (intervalStatePattern r) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_finite _).comp (measurable_pi_apply _)

lemma intervalStatePattern_preimage_singleton (r : ℕ)
    (p : Fin (2 * r + 1) → Fin 2) :
    intervalStatePattern r ⁻¹' {p} = blockStateEvent r p := by
  ext sigma
  change intervalStatePattern r sigma = p ↔ ∀ i,
    boolTransferState (sigma (site1 (-(r : ℤ) + (i.val : ℤ)))) = p i
  exact funext_iff

theorem map_intervalStatePattern_eq_of_block_eq
    {mu nu : Measure (ConfigSpace (Site 1))} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p)) (r : ℕ) :
    Measure.map (intervalStatePattern r) mu = Measure.map (intervalStatePattern r) nu := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_intervalStatePattern r) (measurableSet_singleton p),
    Measure.map_apply (measurable_intervalStatePattern r) (measurableSet_singleton p),
    intervalStatePattern_preimage_singleton]
  have hr := hblock r p
  unfold Measure.real at hr
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu _) (measure_ne_top nu _)).mp hr


end StatMech.FrontierB
