/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace PeriodicPlanarDualPair

variable [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem period_eq
    (D : PeriodicPlanarDualPair P Pdual) :
    D.primalEmbedding.period = D.dualEmbedding.period := by
  apply AddMonoidHom.ext
  intro z
  apply D.primalEmbedding.coordinates.injective
  ext i
  rw [D.primalEmbedding.coordinates_period]
  have h := D.dualEmbedding.coordinates_period z i
  rw [← D.coordinates_eq] at h
  exact h.symm


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
