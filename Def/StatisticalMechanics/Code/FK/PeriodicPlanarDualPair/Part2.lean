/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


namespace PeriodicPlanarDualPair

variable [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def freeDualPercolationProbability
    (D : PeriodicPlanarDualPair P Pdual) (p q : ℝ) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.freeBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
      ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real
      ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.percolationEvent)
  else 0


def FreeDualPercolates
    (D : PeriodicPlanarDualPair P Pdual) (p q : ℝ) : Prop :=
  0 < D.freeDualPercolationProbability p q


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
