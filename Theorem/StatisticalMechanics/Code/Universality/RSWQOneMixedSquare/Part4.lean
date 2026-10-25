/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Def.StatisticalMechanics.Code.Universality.RSWQOneMixedSquare.Part3
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.FK

open StatMech.RSW.Box

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rq1_stripDualReflectedSquare_law (n : ℕ) :
    rba_selfDualMeasure.real (rq1_stripDualReflectedSquareEvent n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)) := by
  have h := (rss_stripDualReflection_measurePreserving (n : ℤ)).measureReal_preimage
    (rlc_horizontalCrossing_measurableSet
      (-(n : ℤ)) (n : ℤ) (-(n : ℤ)) (n : ℤ)).nullMeasurableSet
  simpa [rq1_stripDualReflectedSquareEvent, rba_selfDualMeasure] using h


theorem rq1_stripDualReflectedSquare_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rq1_stripDualReflectedSquareEvent n) := by
  rw [rq1_stripDualReflectedSquare_law]
  exact rq1_centeredSquare_crossing_half n hn

end Universality
end StatMech
